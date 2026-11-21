#!/usr/bin/env python3
"""
Single-Pass Parallel Deep Hidden-Pattern Scanner & True-Reachability Verifier
for the 175,187-module Lean 4 source release.

Checks all soundness, metaprogramming, shadowing, and comment-nesting vectors across
BOTH properly lexed Lean code (respecting nested /- ... -/, -- ..., strings, char
literals, guillemet identifiers) AND raw unstripped text. Simultaneously parses
Unicode-aware imports in the same pass to cross-check DuckDB reachability against
true reachability from Main.
"""

from __future__ import annotations

import argparse
import bisect
import json
import os
import re
import time
from collections import Counter, defaultdict, deque
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

from index_lean import add_path_arguments, resolve_paths

# ---------------------------------------------------------------------------
# Pattern definitions
# ---------------------------------------------------------------------------
PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    # Core kernel / soundness axioms & escapes
    ("sorryAx", re.compile(r"\bsorryAx\b")),
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom", re.compile(r"\baxiom\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("Lean.ofReduceBool", re.compile(r"\b(?:Lean\.)?ofReduceBool\b")),
    ("Lean.ofReduceNat", re.compile(r"\b(?:Lean\.)?ofReduceNat\b")),
    ("Lean.trustCompiler", re.compile(r"\b(?:Lean\.)?trustCompiler\b")),
    ("Lean.reduceBool_Nat", re.compile(r"\b(?:Lean\.)?reduce(?:Bool|Nat)\b")),
    ("lcProof", re.compile(r"\blcProof\b")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("extern", re.compile(r"\bextern\b")),
    ("opaque", re.compile(r"\bopaque\b")),
    ("csimp_CSimp", re.compile(r"\b(?:csimp|CSimp)\b")),
    # Kernel / environment manipulation & metaprogramming
    ("addDecl", re.compile(r"\b(?:addDecl|addDeclCore|addDeclWithoutChecking)\b")),
    ("addAxiom", re.compile(r"\b(?:addAxiom|axiomDecl|mkAxiom)\b")),
    ("modifyEnv_setEnv", re.compile(r"\b(?:modifyEnv|setEnv|addAndCompile|unsafeBaseIO|unsafeIO|unsafeCast)\b")),
    ("import_Lean", re.compile(r"^[ \t]*(?:public[ \t]+|private[ \t]+)?import[ \t]+Lean(?:\.|\b)", re.MULTILINE)),
    ("elab", re.compile(r"\belab(?:_rules)?\b")),
    ("macro", re.compile(r"\bmacro(?:_rules)?\b")),
    ("macro_global", re.compile(r"^[ \t]*macro(?:_rules)?\b", re.MULTILINE)),
    ("syntax", re.compile(r"\b(?:declare_syntax_cat|syntax)\b")),
    ("run_cmd", re.compile(r"\b(?:run_cmd|run_elab|run_meta)\b")),
    ("initialize_cmd", re.compile(r"^[ \t]*(?:builtin_)?initialize\b", re.MULTILINE)),
    ("partial_def", re.compile(r"\bpartial[ \t]+(?:def|abbrev|instance|theorem|lemma|private|protected|noncomputable|unsafe)\b")),
    ("set_option", re.compile(r"\bset_option[ \t]+([A-Za-z0-9_.]+)(?:[ \t]+([^\n;]+))?")),
    # Target statement / Mathlib shadowing checks
    ("def_riemannZeta", re.compile(r"\b(?:def|abbrev|opaque|axiom|structure|class|inductive|notation|macro|syntax)[ \t]+[^\n:=]*\briemannZeta\b")),
    ("def_RiemannHypothesis", re.compile(r"\b(?:def|abbrev|opaque|axiom|structure|class|inductive|notation|macro|syntax)[ \t]+[^\n:=]*\bRiemannHypothesis\b")),
    ("def_LFunction", re.compile(r"\b(?:def|abbrev|opaque|axiom|structure|class|inductive|notation|macro|syntax)[ \t]+[^\n:=]*\bLFunction\b")),
    ("def_DirichletCharacter", re.compile(r"\b(?:def|abbrev|opaque|axiom|structure|class|inductive|notation|macro|syntax)[ \t]+[^\n:=]*\bDirichletCharacter\b")),
    ("notation_cmd", re.compile(r"^[ \t]*(?:(?:local|scoped)[ \t]+)?(?:notation|infixl?|infixr|prefix|postfix)\b", re.MULTILINE)),
    ("notation_global", re.compile(r"^[ \t]*(?:notation|infixl?|infixr|prefix|postfix)\b", re.MULTILINE)),
]

# Fast pre-filter regex matching ANY of the above tokens (single C-level scan per file)
PREFILTER_RE = re.compile(
    r"\b(?:sorryAx|sorry|admit|axiom|native_decide|ofReduceBool|ofReduceNat|trustCompiler|reduceBool|reduceNat|lcProof|"
    r"unsafe|implemented_by|extern|opaque|csimp|CSimp|addDecl|addDeclCore|addDeclWithoutChecking|"
    r"addAxiom|axiomDecl|mkAxiom|modifyEnv|setEnv|addAndCompile|unsafeBaseIO|unsafeIO|unsafeCast|"
    r"elab|elab_rules|macro|macro_rules|syntax|declare_syntax_cat|"
    r"run_cmd|run_elab|run_meta|initialize|builtin_initialize|"
    r"partial|set_option|notation|infix|infixl|infixr|prefix|postfix|"
    r"riemannZeta|RiemannHypothesis|LFunction|DirichletCharacter)\b|"
    r"^[ \t]*(?:public[ \t]+|private[ \t]+)?import[ \t]+Lean(?:\.|\b)",
    re.MULTILINE,
)

# Unicode-aware import header regex
IMPORT_LINE_RE = re.compile(r"^[ \t]*(?:public[ \t]+|private[ \t]+)?import[ \t]+([^\s\-/]+)")

# Lean 4 lexical tokenizer for comments & strings (handles nested /- ... -/, -- ..., "...", char literals, «...»)
LEX_RE = re.compile(
    r'/-|-/|--[^\n]*|"(?:\\.|[^"\\])*"|(?<![A-Za-z0-9_\'])\'(?:\\.|[^\'\\])\'|«[^»]*»'
)

# Standard benign set_option names (do not need full per-line sample dumps)
ROUTINE_OPTIONS = {
    "maxHeartbeats",
    "autoImplicit",
    "maxSynthPendingDepth",
    "synthInstance.maxHeartbeats",
    "backward.isDefEq.respectTransparency",
    "backward.isDefEq.respectTransparency.types",
    "backward.defeqAttrib.useBackward",
    "maxRecDepth",
    "synthInstance.maxSize",
    "genSizeOfSpec",
    "genInjectivity",
    "pp.fullNames",
}

FULL_DUMP_CATS = {
    "sorryAx", "sorry", "admit", "axiom", "native_decide", "Lean.ofReduceBool",
    "Lean.ofReduceNat", "Lean.trustCompiler", "Lean.reduceBool_Nat", "lcProof", "unsafe", "implemented_by", "extern", "opaque",
    "csimp_CSimp", "addDecl", "addAxiom", "modifyEnv_setEnv", "import_Lean", "elab",
    "macro", "macro_global", "syntax", "run_cmd", "initialize_cmd", "partial_def",
    "def_riemannZeta", "def_RiemannHypothesis", "def_LFunction", "def_DirichletCharacter",
    "notation_global",
}


def build_noncode_spans(text: str) -> tuple[list[tuple[int, int, str]], bool]:
    """
    Scan Lean comments & strings at C speed.
    Returns (spans, unbalanced_block_comment) where each span is (start, end, region_type)
    with region_type in ('block_comment', 'line_comment', 'string').
    """
    spans: list[tuple[int, int, str]] = []
    block_depth = 0
    block_start = -1
    for m in LEX_RE.finditer(text):
        tok = m.group(0)
        if block_depth > 0:
            if tok == "/-":
                block_depth += 1
            elif tok == "-/":
                block_depth -= 1
                if block_depth == 0:
                    spans.append((block_start, m.end(), "block_comment"))
            continue

        if tok == "/-":
            block_depth = 1
            block_start = m.start()
        elif tok == "-/":
            return spans, True
        elif tok.startswith("--"):
            spans.append((m.start(), m.end(), "line_comment"))
        elif tok.startswith('"'):
            spans.append((m.start(), m.end(), "string"))

    unbalanced = block_depth != 0
    if block_depth > 0:
        spans.append((block_start, len(text), "block_comment"))
    return spans, unbalanced


def classify_pos(pos: int, span_starts: list[int], spans: list[tuple[int, int, str]]) -> str:
    idx = bisect.bisect_right(span_starts, pos) - 1
    if idx >= 0:
        s, e, kind = spans[idx]
        if s <= pos < e:
            return kind
    return "code"


def build_line_starts(text: str) -> list[int]:
    starts = [0]
    idx = text.find("\n")
    while idx != -1:
        starts.append(idx + 1)
        idx = text.find("\n", idx + 1)
    return starts


def pos_to_line_info(pos: int, line_starts: list[int], text: str) -> tuple[int, str]:
    ln_idx = bisect.bisect_right(line_starts, pos) - 1
    start = line_starts[ln_idx]
    end = line_starts[ln_idx + 1] - 1 if (ln_idx + 1 < len(line_starts)) else len(text)
    line_str = text[start:end].rstrip("\r")
    return ln_idx + 1, line_str.strip()[:260]


def extract_unicode_imports(text: str) -> list[str]:
    """Fast header-only Unicode-aware import extraction."""
    imps: list[str] = []
    pos = 0
    n = len(text)
    in_block = 0
    while pos < n:
        nl = text.find("\n", pos)
        line = text[pos:] if nl == -1 else text[pos:nl]
        pos = n if nl == -1 else nl + 1
        s = line.strip()
        if not s:
            continue
        if in_block > 0 or s.startswith("/-"):
            in_block += s.count("/-") - s.count("-/")
            if in_block < 0:
                in_block = 0
            continue
        if s.startswith("--"):
            continue
        if s.startswith("import ") or s.startswith("public import ") or s.startswith("private import "):
            m = IMPORT_LINE_RE.match(line)
            if m:
                imps.append(m.group(1))
            continue
        break
    return imps


def scan_batch(args: tuple[str, list[tuple[str, str, bool]]]):
    src_root_str, items = args
    src_root = Path(src_root_str)

    hit_counts: Counter[tuple[str, str, bool]] = Counter()
    mod_sets: dict[tuple[str, str, bool], set[str]] = defaultdict(set)
    option_counts: Counter[tuple[str, str, str, bool]] = Counter()
    nonroutine_option_samples: dict[str, list[tuple[str, str, int, str]]] = defaultdict(list)
    samples: dict[tuple[str, str, bool], list[tuple[str, str, int, str]]] = defaultdict(list)
    unbalanced_files: list[tuple[str, str, bool, int, int]] = []
    string_comment_tokens: list[tuple[str, str, bool, int, str]] = []
    read_errors: list[str] = []
    unicode_import_edges: list[tuple[str, list[str]]] = []

    files_scanned = 0

    for mod, rel, db_reachable in items:
        full_path = src_root / rel
        try:
            raw = full_path.read_bytes()
        except OSError as e:
            read_errors.append(f"{rel}: {e}")
            continue
        files_scanned += 1
        text = raw.decode("utf-8", errors="replace")

        # Extract Unicode-aware imports for true reachability check
        imps = extract_unicode_imports(text)
        if imps:
            unicode_import_edges.append((mod, imps))

        has_block_open = "/-" in text
        has_block_close = "-/" in text
        has_prefilter = PREFILTER_RE.search(text) is not None

        if not has_prefilter:
            if has_block_open or has_block_close:
                _spans, unbal = build_noncode_spans(text)
                if unbal:
                    unbalanced_files.append(
                        (mod, rel, db_reachable, text.count("/-"), text.count("-/"))
                    )
            continue

        spans, unbal = build_noncode_spans(text)
        if unbal:
            unbalanced_files.append(
                (mod, rel, db_reachable, text.count("/-"), text.count("-/"))
            )
        span_starts = [s[0] for s in spans]
        line_starts: list[int] | None = None

        for s_start, s_end, s_kind in spans:
            if s_kind == "string":
                frag = text[s_start:s_end]
                if "/-" in frag or "-/" in frag:
                    if line_starts is None:
                        line_starts = build_line_starts(text)
                    ln, snip = pos_to_line_info(s_start, line_starts, text)
                    if len(string_comment_tokens) < 50:
                        string_comment_tokens.append((mod, rel, db_reachable, ln, snip))

        for cat, pat in PATTERNS:
            for m in pat.finditer(text):
                pos = m.start()
                region = classify_pos(pos, span_starts, spans)
                key = (cat, region, db_reachable)
                hit_counts[key] += 1
                mod_sets[key].add(mod)

                if cat == "set_option":
                    opt_name = m.group(1)
                    opt_val = (m.group(2) or "").strip()
                    if " in" in opt_val:
                        opt_val = opt_val.split(" in", 1)[0].strip()
                    if "--" in opt_val:
                        opt_val = opt_val.split("--", 1)[0].strip()
                    option_counts[(opt_name, opt_val[:60], region, db_reachable)] += 1
                    if (
                        region == "code"
                        and opt_name not in ROUTINE_OPTIONS
                        and not opt_name.startswith("linter.")
                        and len(nonroutine_option_samples[opt_name]) < 50
                    ):
                        if line_starts is None:
                            line_starts = build_line_starts(text)
                        ln, snip = pos_to_line_info(pos, line_starts, text)
                        nonroutine_option_samples[opt_name].append((mod, rel, ln, snip))

                cap = 500 if cat in FULL_DUMP_CATS else 30
                if len(samples[key]) < cap:
                    if line_starts is None:
                        line_starts = build_line_starts(text)
                    ln, snip = pos_to_line_info(pos, line_starts, text)
                    samples[key].append((mod, rel, ln, snip))

    mod_counts = {k: len(v) for k, v in mod_sets.items()}
    return (
        files_scanned,
        dict(hit_counts),
        mod_counts,
        dict(option_counts),
        dict(nonroutine_option_samples),
        dict(samples),
        unbalanced_files,
        string_comment_tokens,
        read_errors,
        unicode_import_edges,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Run static dependency and declaration audits.")
    add_path_arguments(parser)
    src_root, db_path, out_dir = resolve_paths(parser.parse_args())

    import duckdb

    out_dir.mkdir(parents=True, exist_ok=True)
    out_json = out_dir / "deep_audit_results.json"

    t0 = time.perf_counter()
    con = duckdb.connect(str(db_path), read_only=True)
    rows = con.execute(
        """
        SELECT m.module, m.rel_path, COALESCE(r.reachable, FALSE) AS reachable
        FROM modules m
        LEFT JOIN reachability r ON m.module = r.module
        ORDER BY m.module
        """
    ).fetchall()
    con.close()

    all_local_mods = {r[0] for r in rows}
    db_reach_count = sum(1 for r in rows if r[2])

    disk_files = 0
    for _dp, _dn, fns in os.walk(str(src_root)):
        for fn in fns:
            if fn.endswith(".lean"):
                disk_files += 1

    t1 = time.perf_counter()
    print(
        f"[1/3] Loaded {len(rows):,} modules from DuckDB (db_reachable={db_reach_count:,}, disk={disk_files:,}) in {t1 - t0:.2f}s",
        flush=True,
    )

    workers = max(1, min(os.cpu_count() or 8, 16))
    batch_size = 1500
    batches = [
        (str(src_root), rows[i : i + batch_size])
        for i in range(0, len(rows), batch_size)
    ]

    total_scanned = 0
    agg_hits: Counter[tuple[str, str, bool]] = Counter()
    agg_mods: Counter[tuple[str, str, bool]] = Counter()
    agg_opts: Counter[tuple[str, str, str, bool]] = Counter()
    agg_nonroutine_opts: dict[str, list[tuple[str, str, int, str]]] = defaultdict(list)
    agg_samples: dict[tuple[str, str, bool], list[tuple[str, str, int, str]]] = defaultdict(list)
    all_unbalanced: list[tuple[str, str, bool, int, int]] = []
    all_str_comments: list[tuple[str, str, bool, int, str]] = []
    all_errors: list[str] = []
    adj: dict[str, list[str]] = {}

    print(f"[2/3] Scanning {len(rows):,} files with {workers} workers ...", flush=True)
    with ProcessPoolExecutor(max_workers=workers) as ex:
        for (
            n_scan,
            hc,
            mc,
            oc,
            nro,
            samp,
            unbal,
            scomm,
            errs,
            imp_edges,
        ) in ex.map(scan_batch, batches):
            total_scanned += n_scan
            agg_hits.update(hc)
            agg_mods.update(mc)
            agg_opts.update(oc)
            for oname, v in nro.items():
                cur = agg_nonroutine_opts[oname]
                if len(cur) < 60:
                    cur.extend(v[: 60 - len(cur)])
            for k, v in samp.items():
                cat = k[0]
                cap = 500 if cat in FULL_DUMP_CATS else 50
                cur = agg_samples[k]
                if len(cur) < cap:
                    cur.extend(v[: cap - len(cur)])
            all_unbalanced.extend(unbal)
            all_str_comments.extend(scomm)
            all_errors.extend(errs)
            for src_m, dsts in imp_edges:
                local_dsts = [d for d in dsts if d in all_local_mods]
                if local_dsts:
                    adj[src_m] = local_dsts

    # Compute true Unicode-aware reachability from Main
    true_depth: dict[str, int] = {"Main": 0}
    q = deque([("Main", 0)])
    while q:
        u, d = q.popleft()
        for v in adj.get(u, ()):
            if v not in true_depth:
                true_depth[v] = d + 1
                q.append((v, d + 1))

    true_reach_count = len(true_depth)
    true_unreach = sorted(all_local_mods - set(true_depth.keys()))

    t2 = time.perf_counter()
    print(
        f"[3/3] Scan complete: {total_scanned:,} files in {t2 - t1:.2f}s (total {t2 - t0:.2f}s) | "
        f"True reachable from Main: {true_reach_count:,}/{len(rows):,} (unreachable={len(true_unreach):,})",
        flush=True,
    )

    cats = [c for c, _ in PATTERNS]
    summary = {}
    for cat in cats:
        code_db_reach = agg_hits.get((cat, "code", True), 0)
        code_db_unreach = agg_hits.get((cat, "code", False), 0)
        code_total = code_db_reach + code_db_unreach
        comment_reach = agg_hits.get((cat, "block_comment", True), 0) + agg_hits.get((cat, "line_comment", True), 0)
        comment_unreach = agg_hits.get((cat, "block_comment", False), 0) + agg_hits.get((cat, "line_comment", False), 0)
        str_reach = agg_hits.get((cat, "string", True), 0)
        str_unreach = agg_hits.get((cat, "string", False), 0)
        cap_out = 500 if cat in FULL_DUMP_CATS else 30
        summary[cat] = {
            "code_total": code_total,
            "code_db_reachable": code_db_reach,
            "code_db_unreachable": code_db_unreach,
            "code_true_reachable": code_total if len(true_unreach) == 0 else None,
            "code_db_reachable_mods": agg_mods.get((cat, "code", True), 0),
            "code_db_unreachable_mods": agg_mods.get((cat, "code", False), 0),
            "comment_total": comment_reach + comment_unreach,
            "string_total": str_reach + str_unreach,
            "raw_total": code_total + comment_reach + comment_unreach + str_reach + str_unreach,
            "samples_code_reachable": agg_samples.get((cat, "code", True), [])[:cap_out],
            "samples_code_unreachable": agg_samples.get((cat, "code", False), [])[:cap_out],
            "samples_comment": (
                agg_samples.get((cat, "line_comment", True), [])[:10]
                + agg_samples.get((cat, "block_comment", True), [])[:10]
            ),
            "samples_string": agg_samples.get((cat, "string", True), [])[:10],
        }

    opt_by_name: dict[str, dict[str, int]] = defaultdict(lambda: {"code_db_reach": 0, "code_db_unreach": 0, "comment": 0})
    opt_top_pairs: list[tuple[str, str, str, bool, int]] = []
    for (oname, oval, reg, rch), cnt in agg_opts.most_common(120):
        opt_top_pairs.append((oname, oval, reg, rch, cnt))
    for (oname, _oval, reg, rch), cnt in agg_opts.items():
        if reg == "code":
            if rch:
                opt_by_name[oname]["code_db_reach"] += cnt
            else:
                opt_by_name[oname]["code_db_unreach"] += cnt
        else:
            opt_by_name[oname]["comment"] += cnt

    result = {
        "meta": {
            "duckdb_modules": len(rows),
            "disk_lean_files": disk_files,
            "files_scanned": total_scanned,
            "db_reachable_modules": db_reach_count,
            "db_unreachable_modules": len(rows) - db_reach_count,
            "true_reachable_modules": true_reach_count,
            "true_unreachable_modules": len(true_unreach),
            "true_max_depth_from_main": max(true_depth.values()) if true_depth else -1,
            "read_errors": len(all_errors),
            "elapsed_sec": round(t2 - t0, 2),
            "scan_sec": round(t2 - t1, 2),
        },
        "summary": summary,
        "set_option_by_name": dict(sorted(opt_by_name.items(), key=lambda kv: -(kv[1]["code_db_reach"] + kv[1]["code_db_unreach"]))),
        "set_option_top_pairs": opt_top_pairs,
        "nonroutine_option_samples": dict(agg_nonroutine_opts),
        "unbalanced_block_comments": all_unbalanced[:50],
        "unbalanced_block_comments_count": len(all_unbalanced),
        "string_comment_tokens": all_str_comments[:50],
        "string_comment_tokens_count": len(all_str_comments),
        "read_errors_sample": all_errors[:20],
    }

    out_json.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"Saved JSON report to {out_json}\n", flush=True)

    print(f"{'Category':24s} | {'CodeTot':>8s} | {'DB_Rch':>8s} | {'DB_Unr':>7s} | {'Comm':>6s} | {'Str':>5s} | {'RawTot':>8s}")
    print("-" * 82)
    for cat in cats:
        s = summary[cat]
        print(
            f"{cat:24s} | {s['code_total']:8,d} | {s['code_db_reachable']:8,d} | "
            f"{s['code_db_unreachable']:7,d} | {s['comment_total']:6,d} | "
            f"{s['string_total']:5,d} | {s['raw_total']:8,d}"
        )


if __name__ == "__main__":
    main()
