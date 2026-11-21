#!/usr/bin/env python3
"""
Fast Stage 0 Static Indexer & Statement Auditor for massive Lean 4 repositories.
Parses all .lean files under <root>/src in parallel, writes TSVs, bulk-loads into
DuckDB via read_csv (100x faster than executemany), computes reachability from Main,
and generates an audit + spine summary report.
"""

from __future__ import annotations

import argparse
import csv
import os
import re
import time
from collections import deque
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SRC_ROOT = PROJECT_ROOT / "lean" / "src"
DEFAULT_OUT_DIR = PROJECT_ROOT / "out"
DEFAULT_INDEX_DB = DEFAULT_OUT_DIR / "lean_index.duckdb"


def add_path_arguments(parser: argparse.ArgumentParser, *, uses_index: bool = True) -> None:
    parser.add_argument("--src-root", type=Path, help="Lean src/ directory (default: LEAN_SRC_ROOT or lean/src)")
    if uses_index:
        parser.add_argument("--index-db", type=Path, help="DuckDB index (default: LEAN_INDEX_DB or OUT_DIR/lean_index.duckdb)")
    parser.add_argument("--out-dir", type=Path, help="Generated output directory (default: OUT_DIR or out)")


def resolve_paths(args: argparse.Namespace) -> tuple[Path, Path, Path]:
    legacy_root = getattr(args, "lean_project", None)
    if legacy_root is not None:
        legacy_root = legacy_root / "src"
    src_root = args.src_root or legacy_root or Path(os.environ.get("LEAN_SRC_ROOT") or DEFAULT_SRC_ROOT)
    out_dir = args.out_dir or getattr(args, "output_directory", None) or Path(os.environ.get("OUT_DIR") or DEFAULT_OUT_DIR)
    index_db = getattr(args, "index_db", None) or Path(os.environ.get("LEAN_INDEX_DB") or out_dir / "lean_index.duckdb")
    return src_root, index_db, out_dir


# Regex patterns (fast, line-oriented)
RE_IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?import\s+([A-Za-z0-9_.'`]+)")
RE_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|axiom|structure|class|inductive|opaque|instance)\b(?:\s+([^\s:({\[=]+))?"
)
RE_AUDIT_PATTERNS = [
    ("axiom", re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|unsafe)\s+)*axiom\b")),
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("unsafe", re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*unsafe\b")),
    ("extern", re.compile(r"@\[[^\]]*\bextern\b")),
    ("opaque", re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*opaque\b")),
]


def clean_field(s: str) -> str:
    return s.replace("\t", " ").replace("\r", " ").replace("\n", " ")


def parse_batch(args: tuple[str, list[str]]) -> tuple[list, list, list, list]:
    src_root_str, rel_paths = args
    src_root = Path(src_root_str)

    modules_rows = []
    imports_rows = []
    decls_rows = []
    audit_rows = []

    for rel in rel_paths:
        full_path = src_root / rel
        mod_name = rel[:-5].replace("\\", ".").replace("/", ".")
        top_lib = mod_name.split(".", 1)[0]

        try:
            raw = full_path.read_bytes()
        except OSError:
            continue

        byte_len = len(raw)
        text = raw.decode("utf-8", errors="replace")
        lines = text.splitlines()
        line_count = len(lines)

        in_block_comment = 0
        mod_imports: list[str] = []
        has_mathlib = False
        has_sorry = False
        has_axiom = False
        has_native_decide = False
        has_unsafe = False

        file_decls: list[list] = []
        collecting_sig = False

        for idx, line in enumerate(lines, start=1):
            s = line
            if "/-" in s or "-/" in s or in_block_comment > 0:
                out_chars = []
                i = 0
                n = len(s)
                while i < n:
                    if s[i : i + 2] == "/-":
                        in_block_comment += 1
                        i += 2
                    elif s[i : i + 2] == "-/" and in_block_comment > 0:
                        in_block_comment -= 1
                        i += 2
                    else:
                        if in_block_comment == 0:
                            out_chars.append(s[i])
                        i += 1
                s = "".join(out_chars)

            cidx = s.find("--")
            code = s[:cidx] if cidx != -1 else s
            stripped = code.strip()
            if not stripped:
                continue

            if stripped.startswith("import ") or "import " in stripped[:20]:
                m_imp = RE_IMPORT.match(code)
                if m_imp:
                    target = m_imp.group(1)
                    mod_imports.append(target)
                    if target == "Mathlib" or target.startswith("Mathlib."):
                        has_mathlib = True
                    continue

            # Quick substring pre-filter before regex for audit patterns
            if (
                "axiom" in code
                or "sorry" in code
                or "admit" in code
                or "native_decide" in code
                or "implemented_by" in code
                or "unsafe" in code
                or "extern" in code
                or "opaque" in code
            ):
                for akind, apat in RE_AUDIT_PATTERNS:
                    if apat.search(code):
                        if akind == "sorry":
                            has_sorry = True
                        elif akind == "axiom":
                            has_axiom = True
                        elif akind == "native_decide":
                            has_native_decide = True
                        elif akind in ("unsafe", "implemented_by", "extern"):
                            has_unsafe = True
                        audit_rows.append((mod_name, idx, akind, clean_field(stripped[:240])))

            if not code[0].isspace() or code.startswith("  "):
                m_decl = RE_DECL.match(code)
                if m_decl:
                    kind = m_decl.group(1)
                    name = m_decl.group(2) or "<anonymous>"
                    sig_part = stripped
                    if ":=" in sig_part:
                        sig_part = sig_part.split(":=", 1)[0].strip()
                        collecting_sig = False
                    else:
                        collecting_sig = True
                    file_decls.append([kind, name, idx, [sig_part]])
                    continue

            if collecting_sig and file_decls:
                if ":=" in stripped:
                    before = stripped.split(":=", 1)[0].strip()
                    if before:
                        file_decls[-1][3].append(before)
                    collecting_sig = False
                elif stripped.startswith("where"):
                    collecting_sig = False
                else:
                    if sum(len(x) for x in file_decls[-1][3]) < 400:
                        file_decls[-1][3].append(stripped)
                    else:
                        collecting_sig = False

        for i, d in enumerate(file_decls):
            start_ln = d[2]
            end_ln = (file_decls[i + 1][2] - 1) if (i + 1 < len(file_decls)) else line_count
            span = max(1, end_ln - start_ln + 1)
            sig = clean_field(" ".join(d[3])[:500])
            decls_rows.append((mod_name, d[0], d[1], start_ln, end_ln, span, sig))

        for dst in mod_imports:
            imports_rows.append((mod_name, dst))

        modules_rows.append(
            (
                mod_name,
                top_lib,
                rel,
                byte_len,
                line_count,
                int(has_sorry),
                int(has_axiom),
                int(has_native_decide),
                int(has_unsafe),
                int(has_mathlib),
                len(mod_imports),
                len(file_decls),
            )
        )

    return modules_rows, imports_rows, decls_rows, audit_rows


def collect_lean_files(src_root: Path) -> list[str]:
    rel_paths: list[str] = []
    root_str = str(src_root)
    prefix_len = len(root_str) + 1
    for dirpath, _dirnames, filenames in os.walk(root_str):
        for fn in filenames:
            if fn.endswith(".lean"):
                rel_paths.append(os.path.join(dirpath, fn)[prefix_len:])
    return rel_paths


def main() -> None:
    parser = argparse.ArgumentParser(description="Build the static Lean source index.")
    add_path_arguments(parser)
    parser.add_argument("lean_project", type=Path, nargs="?", help="Legacy Lean project root (contains src/)")
    parser.add_argument("output_directory", type=Path, nargs="?", help="Legacy output directory")
    src_root, db_path, out_dir = resolve_paths(parser.parse_args())
    if not src_root.is_dir():
        parser.error(f"Lean source directory does not exist: {src_root}")
    if db_path.exists():
        parser.error(f"index already exists: {db_path}; choose a fresh --index-db to rebuild")

    import duckdb  # import only in main process, not in spawned workers

    out_dir.mkdir(parents=True, exist_ok=True)
    db_path.parent.mkdir(parents=True, exist_ok=True)
    report_path = out_dir / "audit_summary.md"
    tmp_dir = out_dir / "_tsv"
    tmp_dir.mkdir(exist_ok=True)

    t0 = time.perf_counter()
    print(f"[1/5] Scanning .lean files under {src_root} ...", flush=True)
    rel_paths = collect_lean_files(src_root)
    t1 = time.perf_counter()
    print(f"      Found {len(rel_paths):,} .lean files in {t1 - t0:.2f}s", flush=True)

    workers = max(1, min(os.cpu_count() or 4, 16))
    batch_size = 1000
    batches = [
        (str(src_root), rel_paths[i : i + batch_size])
        for i in range(0, len(rel_paths), batch_size)
    ]

    f_mod = tmp_dir / "modules.tsv"
    f_imp = tmp_dir / "imports.tsv"
    f_dec = tmp_dir / "decls.tsv"
    f_aud = tmp_dir / "audit_hits.tsv"
    f_rch = tmp_dir / "reachability.tsv"

    print(f"[2/5] Parsing {len(rel_paths):,} files with {workers} workers -> TSV ...", flush=True)
    done_files = 0
    local_mods: set[str] = set()
    adj: dict[str, list[str]] = {}
    all_imports: list[tuple[str, str]] = []

    with (
        open(f_mod, "w", encoding="utf-8", newline="") as wm,
        open(f_imp, "w", encoding="utf-8", newline="") as wi,
        open(f_dec, "w", encoding="utf-8", newline="") as wd,
        open(f_aud, "w", encoding="utf-8", newline="") as wa,
        ProcessPoolExecutor(max_workers=workers) as ex,
    ):
        cm = csv.writer(wm, delimiter="\t", quoting=csv.QUOTE_MINIMAL)
        ci = csv.writer(wi, delimiter="\t", quoting=csv.QUOTE_MINIMAL)
        cd = csv.writer(wd, delimiter="\t", quoting=csv.QUOTE_MINIMAL)
        ca = csv.writer(wa, delimiter="\t", quoting=csv.QUOTE_MINIMAL)

        cm.writerow(["module", "top_lib", "rel_path", "bytes", "lines", "has_sorry", "has_axiom", "has_native_decide", "has_unsafe", "has_mathlib_import", "import_count", "decl_count"])
        ci.writerow(["src_module", "dst_module"])
        cd.writerow(["module", "kind", "name", "start_line", "end_line", "span_lines", "signature"])
        ca.writerow(["module", "line_no", "kind", "snippet"])

        for mod_rows, imp_rows, decl_rows, aud_rows in ex.map(parse_batch, batches):
            cm.writerows(mod_rows)
            ci.writerows(imp_rows)
            cd.writerows(decl_rows)
            ca.writerows(aud_rows)
            for mr in mod_rows:
                local_mods.add(mr[0])
            all_imports.extend(imp_rows)
            done_files += len(mod_rows)
            if done_files % 25000 < batch_size or done_files == len(rel_paths):
                print(f"      Parsed {done_files:,} / {len(rel_paths):,} ({time.perf_counter() - t1:.1f}s)", flush=True)

    t2 = time.perf_counter()
    print(f"[3/5] Computing import DAG & reachability from Main ({t2 - t1:.2f}s parse) ...", flush=True)

    in_deg: dict[str, int] = {m: 0 for m in local_mods}
    for src, dst in all_imports:
        if dst in local_mods:
            adj.setdefault(src, []).append(dst)
            in_deg[dst] = in_deg.get(dst, 0) + 1
    del all_imports

    depth: dict[str, int] = {}
    if "Main" in local_mods:
        q = deque([("Main", 0)])
        depth["Main"] = 0
        while q:
            u, d = q.popleft()
            for v in adj.get(u, ()):
                if v not in depth:
                    depth[v] = d + 1
                    q.append((v, d + 1))

    with open(f_rch, "w", encoding="utf-8", newline="") as wr:
        cr = csv.writer(wr, delimiter="\t", quoting=csv.QUOTE_MINIMAL)
        cr.writerow(["module", "reachable", "depth_from_main", "in_degree", "local_out_degree"])
        for m in local_mods:
            cr.writerow((m, int(m in depth), depth.get(m, -1), in_deg.get(m, 0), len(adj.get(m, ()))))

    t3 = time.perf_counter()
    print(f"[4/5] Bulk-loading TSVs into DuckDB ({t3 - t2:.2f}s DAG) ...", flush=True)

    con = duckdb.connect(str(db_path))

    def load_tsv(table: str, path: Path, cols: str) -> None:
        p = str(path).replace("\\", "/")
        con.execute(
            f"CREATE TABLE {table} AS SELECT * FROM read_csv('{p}', delim='\t', header=true, quote='\"', escape='\"', columns={cols});"
        )

    load_tsv(
        "modules",
        f_mod,
        "{'module':'VARCHAR','top_lib':'VARCHAR','rel_path':'VARCHAR','bytes':'BIGINT','lines':'INTEGER','has_sorry':'BOOLEAN','has_axiom':'BOOLEAN','has_native_decide':'BOOLEAN','has_unsafe':'BOOLEAN','has_mathlib_import':'BOOLEAN','import_count':'INTEGER','decl_count':'INTEGER'}",
    )
    load_tsv("imports", f_imp, "{'src_module':'VARCHAR','dst_module':'VARCHAR'}")
    load_tsv(
        "decls",
        f_dec,
        "{'module':'VARCHAR','kind':'VARCHAR','name':'VARCHAR','start_line':'INTEGER','end_line':'INTEGER','span_lines':'INTEGER','signature':'VARCHAR'}",
    )
    load_tsv("audit_hits", f_aud, "{'module':'VARCHAR','line_no':'INTEGER','kind':'VARCHAR','snippet':'VARCHAR'}")
    load_tsv(
        "reachability",
        f_rch,
        "{'module':'VARCHAR','reachable':'BOOLEAN','depth_from_main':'INTEGER','in_degree':'INTEGER','local_out_degree':'INTEGER'}",
    )

    t4 = time.perf_counter()
    print(f"[5/5] Generating audit summary ({t4 - t3:.2f}s DuckDB load) ...", flush=True)

    tot = con.execute(
        """
        SELECT
            COUNT(*),
            SUM(lines),
            SUM(bytes),
            SUM(decl_count),
            SUM(CASE WHEN r.reachable THEN 1 ELSE 0 END),
            SUM(CASE WHEN r.reachable THEN m.lines ELSE 0 END),
            SUM(CASE WHEN r.reachable THEN m.bytes ELSE 0 END),
            MAX(r.depth_from_main)
        FROM modules m
        JOIN reachability r USING (module)
        """
    ).fetchone()

    by_lib = con.execute(
        """
        SELECT
            m.top_lib,
            COUNT(*) AS total_mods,
            SUM(CASE WHEN r.reachable THEN 1 ELSE 0 END) AS reach_mods,
            SUM(m.lines) AS total_lines,
            SUM(CASE WHEN r.reachable THEN m.lines ELSE 0 END) AS reach_lines,
            SUM(CASE WHEN m.has_mathlib_import THEN 1 ELSE 0 END) AS mathlib_mods
        FROM modules m
        JOIN reachability r USING (module)
        GROUP BY m.top_lib
        ORDER BY total_lines DESC
        """
    ).fetchall()

    audit_summary = con.execute(
        """
        SELECT
            a.kind,
            COUNT(*) AS total_hits,
            SUM(CASE WHEN r.reachable THEN 1 ELSE 0 END) AS reachable_hits,
            COUNT(DISTINCT CASE WHEN r.reachable THEN a.module END) AS reachable_mods
        FROM audit_hits a
        JOIN reachability r USING (module)
        GROUP BY a.kind
        ORDER BY reachable_hits DESC, total_hits DESC
        """
    ).fetchall()

    reachable_suspicious = con.execute(
        """
        SELECT a.kind, a.module, a.line_no, a.snippet
        FROM audit_hits a
        JOIN reachability r USING (module)
        WHERE r.reachable AND a.kind IN ('axiom', 'sorry', 'admit', 'native_decide', 'implemented_by', 'unsafe', 'extern')
        ORDER BY a.kind, r.depth_from_main, a.module, a.line_no
        LIMIT 80
        """
    ).fetchall()

    top_decls = con.execute(
        """
        SELECT d.span_lines, d.kind, d.module, d.name, d.start_line, r.depth_from_main
        FROM decls d
        JOIN reachability r USING (module)
        WHERE r.reachable AND d.kind IN ('theorem', 'lemma')
        ORDER BY d.span_lines DESC
        LIMIT 25
        """
    ).fetchall()

    top_hubs = con.execute(
        """
        SELECT r.in_degree, r.depth_from_main, m.lines, m.module
        FROM reachability r
        JOIN modules m USING (module)
        WHERE r.reachable
        ORDER BY r.in_degree DESC
        LIMIT 20
        """
    ).fetchall()

    shallow_spine = con.execute(
        """
        SELECT r.depth_from_main, m.module, m.lines, m.decl_count, r.local_out_degree
        FROM reachability r
        JOIN modules m USING (module)
        WHERE r.reachable AND r.depth_from_main BETWEEN 0 AND 3
        ORDER BY r.depth_from_main, m.module
        LIMIT 80
        """
    ).fetchall()

    md: list[str] = []
    md.append("# Stage 0 Static Index & Audit Summary\n")
    md.append(f"- **Source Root**: `{src_root}`")
    md.append(f"- **DuckDB**: `{db_path}`")
    md.append(f"- **Total Modules**: {tot[0]:,} ({tot[1]:,} lines, {tot[2] / (1024**2):.1f} MB, {tot[3]:,} decls)")
    dead_mods = tot[0] - tot[4]
    dead_lines = tot[1] - tot[5]
    md.append(
        f"- **Reachable from `Main`**: {tot[4]:,} modules ({tot[5]:,} lines, {tot[6] / (1024**2):.1f} MB) | "
        f"**Unreachable (Dead)**: {dead_mods:,} modules ({dead_lines:,} lines) | **Max Depth**: {tot[7]}"
    )

    md.append("\n## 1. Library Breakdown\n")
    md.append("| Top Lib | Total Mods | Reachable Mods | Total Lines | Reachable Lines | Imports Mathlib |")
    md.append("| :--- | ---: | ---: | ---: | ---: | ---: |")
    for row in by_lib:
        md.append(f"| `{row[0]}` | {row[1]:,} | {row[2]:,} | {row[3]:,} | {row[4]:,} | {row[5]:,} |")

    md.append("\n## 2. Integrity Audit Hits (`axiom` / `sorry` / `native_decide` / `unsafe` / `opaque`)\n")
    if audit_summary:
        md.append("| Kind | Total Hits | Reachable Hits | Reachable Modules |")
        md.append("| :--- | ---: | ---: | ---: |")
        for row in audit_summary:
            md.append(f"| `{row[0]}` | {row[1]:,} | {row[2]:,} | {row[3]:,} |")
    else:
        md.append("No audit hits detected.")

    if reachable_suspicious:
        md.append("\n### Reachable High-Priority Audit Hits (first 80)\n")
        for kind, mod, ln, snip in reachable_suspicious:
            md.append(f"- `[{kind}]` `{mod}:{ln}` — `{snip}`")

    md.append("\n## 3. Shallow Spine (Depth 0–3 from `Main`)\n")
    md.append("| Depth | Module | Lines | Decls | Local Imports |")
    md.append("| ---: | :--- | ---: | ---: | ---: |")
    for row in shallow_spine:
        md.append(f"| {row[0]} | `{row[1]}` | {row[2]:,} | {row[3]:,} | {row[4]:,} |")

    md.append("\n## 4. Top 25 Largest Reachable Theorems/Lemmas (Proof Golfing Candidates)\n")
    md.append("| Span Lines | Kind | Depth | Module | Name | Start Line |")
    md.append("| ---: | :--- | ---: | :--- | :--- | ---: |")
    for span, kind, mod, name, sln, dep in top_decls:
        md.append(f"| {span:,} | `{kind}` | {dep} | `{mod}` | `{name}` | {sln} |")

    md.append("\n## 5. Top 20 Most-Imported Reachable Hub Modules\n")
    md.append("| In-Degree | Depth | Lines | Module |")
    md.append("| ---: | ---: | ---: | :--- |")
    for indeg, dep, lns, mod in top_hubs:
        md.append(f"| {indeg:,} | {dep} | {lns:,} | `{mod}` |")

    report_text = "\n".join(md) + "\n"
    report_path.write_text(report_text, encoding="utf-8")
    con.close()

    t5 = time.perf_counter()
    print(f"All done in {t5 - t0:.2f}s. Report saved to {report_path}", flush=True)


if __name__ == "__main__":
    main()
