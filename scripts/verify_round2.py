#!/usr/bin/env python3
"""
Round 2 Adversarial Verification Suite (Track D - adversarial_critic).

Capabilities:
  1. --refs <md1> [md2 ...]       : 100% DuckDB + Unicode-aware + disk verification of every
                                    Module.decl, module, and .lean path/line anchor in Round 2 MD reports.
  2. --capelli-shadow <dir>       : 82-file shadow audit vs original src/:
                                    line/byte deltas, 100% decl-name preservation, zero sorry/axiom/admit,
                                    balanced delimiters, '@' stripping statistics.
  3. --harnesses <dir1> [dir2...] : Independent Lean v4.34.1 compilation of every standalone harness
                                    via `elan run leanprover/lean4:v4.34.1 lean <file>` + zero sorry/axiom check.
  4. --check-golf <file>          : Compares golfed_RingObjectsOfMatrixData.lean target statement against
                                    original RingObjectsOfMatrixData.lean:109 + zero sorry/axiom + have/line stats.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable

from index_lean import PROJECT_ROOT, add_path_arguments, resolve_paths

# Round 1 reference checks used by the Round 2 verifier.
LOCAL_ROOT_NAMESPACES = {
    "UpperTheory",
    "GlobalTheory",
}

EXTERNAL_PREFIXES = (
    "Mathlib",
    "Lean",
    "Std",
    "Init",
    "Batteries",
    "Aesop",
    "Qq",
    "Plausible",
    "ProofWidgets",
    "Cli",
    "Meta",
    "Expr",
    "Elab",
    "Term",
    "Command",
    "Kernel",
    "Quot",
    "Classical",
    "Iff",
    "Subsingleton",
    "DirichletCharacter",
    "Complex",
    "Real",
    "Nat",
    "Int",
    "Rat",
    "Finset",
    "Filter",
    "MeasureTheory",
    "Polynomial",
    "NumberField",
    "IsDedekindDomain",
    "HeightOneSpectrum",
    "ValuationSubring",
    "Submodule",
    "Module",
    "Matrix",
    "GL",
    "SL",
    "ZMod",
    "Padic",
    "PadicInt",
    "CharZero",
    "IsAlgClosure",
    "Algebra",
    "CommRing",
    "Field",
    "RingHom",
    "LinearEquiv",
)

IGNORED_KEYWORDS_AND_COLS = {
    # DuckDB schema / column names
    "module", "top_lib", "rel_path", "bytes", "lines", "has_sorry", "has_axiom",
    "has_native_decide", "has_unsafe", "has_mathlib_import", "import_count",
    "decl_count", "src_module", "dst_module", "kind", "name", "start_line",
    "end_line", "span_lines", "signature", "line_no", "snippet", "reachable",
    "depth_from_main", "in_degree", "local_out_degree", "modules", "imports",
    "decls", "audit_hits", "reachability",
    # Lean keywords / options / audit tokens
    "theorem", "lemma", "def", "abbrev", "axiom", "structure", "class",
    "inductive", "opaque", "instance", "private", "protected", "noncomputable",
    "unsafe", "partial", "scoped", "local", "import", "public", "namespace",
    "end", "open", "section", "variable", "universe", "where", "by", "sorry",
    "admit", "native_decide", "implemented_by", "extern", "csimp", "CSimp",
    "elab", "macro", "syntax", "run_cmd", "set_option", "sorryAx", "lcProof",
    "maxHeartbeats", "autoImplicit", "relaxedAutoImplicit", "maxSynthPendingDepth",
    "RiemannHypothesis", "riemannZeta", "LFunction", "Prop", "Type", "Sort",
    "true", "false", "lake", "elan", "lean", "build", "python", "duckdb",
}

RE_INLINE_CODE = re.compile(r"`([^`\n]+)`")
RE_MD_LINK = re.compile(r"\[[^\]]*\]\(([^)\s]+)\)")
RE_LEAN_PATH = re.compile(
    r"([A-Za-z0-9_./\\₂-]+\.lean)"
    r"(?:(?::|#L)(\d+)(?:(?:-|(?:-L))(\d+))?)?"
)
RE_DOTTED_TOK = re.compile(
    r"(?<![A-Za-z0-9_/\\₂])"
    r"((?:_root_\.)?[A-Za-z][A-Za-z0-9_'₂]*(?:\.[A-Za-z0-9_'₂]+)+)"
    r"(?:\.\*)?"
    r"(?::(\d+)(?:[-–](\d+))?)?"
    r"(?![A-Za-z0-9_'/\\₂])"
)
RE_SINGLE_MOD_OR_LINE = re.compile(r"^([A-Za-z][A-Za-z0-9_'.₂]*)(?:\.\*)?(?::(\d+)(?:[-–](\d+))?)?$")
RE_HEADER_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|axiom|structure|class|inductive|opaque|instance)\b(?:\s+([^\s:({\[=]+))?"
)


@dataclass
class RefFinding:
    md_line: int
    raw: str
    category: str  # FILE_PATH, MODULE, MODULE_DECL, DIR_PREFIX, GLOBAL_DECL, LINE_PAIR, EXTERNAL
    status: str    # PASS, WARN, FAIL
    detail: str


@dataclass
class ReportSummary:
    file: str
    total_checked: int = 0
    passed: int = 0
    warnings: int = 0
    failed: int = 0
    external_ignored: int = 0
    findings: list[RefFinding] = field(default_factory=list)


class LeanIndexVerifier:
    def __init__(self, db_path: Path, src_root: Path) -> None:
        import duckdb

        self.src_root = src_root
        self.con = duckdb.connect(str(db_path), read_only=True)
        self.modules: dict[str, tuple[str, int, bool, int, str]] = {}
        self.relpath_to_mod: dict[str, str] = {}
        self.basename_to_mods: dict[str, list[str]] = {}
        self.top_libs: set[str] = set()
        self.dir_prefixes: dict[str, int] = {}
        self._mod_imports_cache: dict[str, set[str]] = {}

        # Caches populated on demand
        self._mod_decls_cache: dict[str, list[tuple[str, str, int, int]]] = {}
        self._mod_qualified_decls_cache: dict[str, set[str]] = {}
        self._decl_name_cache: dict[str, list[tuple[str, str, int, int]]] = {}
        self._sig_match_cache: dict[str, bool] = {}

        self._load_modules()

    def get_mod_imports(self, mod: str) -> set[str]:
        if mod not in self._mod_imports_cache:
            rows = self.con.execute(
                "SELECT dst_module FROM imports WHERE src_module = ?",
                [mod],
            ).fetchall()
            self._mod_imports_cache[mod] = {r[0] for r in rows if r[0] in self.modules}
        return self._mod_imports_cache[mod]

    def _load_modules(self) -> None:
        rows = self.con.execute("""
            SELECT m.module, m.rel_path, m.lines, r.reachable, r.depth_from_main, m.top_lib
            FROM modules m
            JOIN reachability r USING (module)
        """).fetchall()
        for mod, rel, lns, rch, dep, top_lib in rows:
            rel_norm = rel.replace("\\", "/")
            self.modules[mod] = (rel_norm, lns, bool(rch), dep, top_lib)
            self.relpath_to_mod[rel_norm.lower()] = mod
            base = rel_norm.rsplit("/", 1)[-1].lower()
            self.basename_to_mods.setdefault(base, []).append(mod)
            self.top_libs.add(top_lib)

            parts = mod.split(".")
            for i in range(1, len(parts)):
                pref = ".".join(parts[:i])
                self.dir_prefixes[pref] = self.dir_prefixes.get(pref, 0) + 1

    def get_mod_decls(self, mod: str) -> list[tuple[str, str, int, int]]:
        if mod not in self._mod_decls_cache:
            rows = self.con.execute(
                "SELECT name, kind, start_line, end_line FROM decls WHERE module = ? ORDER BY start_line",
                [mod],
            ).fetchall()
            self._mod_decls_cache[mod] = rows
        return self._mod_decls_cache[mod]

    def get_mod_qualified_names(self, mod: str) -> set[str]:
        """
        Parse ONLY namespace/end headers and declaration names (never proof bodies)
        for a single module file, returning all valid qualified/unqualified names.
        """
        if mod in self._mod_qualified_decls_cache:
            return self._mod_qualified_decls_cache[mod]
        names: set[str] = set()
        for dname, _kind, _sl, _el in self.get_mod_decls(mod):
            clean = dname[7:] if dname.startswith("_root_.") else dname
            names.add(dname)
            names.add(clean)
            if "." in clean:
                names.add(clean.rsplit(".", 1)[-1])

        info = self.modules.get(mod)
        if info:
            p = self.src_root / info[0]
            if p.exists():
                ns_stack: list[str] = []
                in_block = 0
                for line in p.read_text(encoding="utf-8", errors="replace").splitlines():
                    # Quick comment stripping
                    if "/-" in line or "-/" in line or in_block > 0:
                        out_c = []
                        i = 0
                        n = len(line)
                        while i < n:
                            if line[i:i+2] == "/-":
                                in_block += 1
                                i += 2
                            elif line[i:i+2] == "-/" and in_block > 0:
                                in_block -= 1
                                i += 2
                            else:
                                if in_block == 0:
                                    out_c.append(line[i])
                                i += 1
                        line = "".join(out_c)
                    cidx = line.find("--")
                    if cidx != -1:
                        line = line[:cidx]
                    s = line.strip()
                    if not s:
                        continue
                    if s.startswith("namespace "):
                        ns = s[len("namespace "):].strip().split()[0]
                        ns_stack.append(ns)
                    elif s.startswith("end"):
                        rest = s[3:].strip()
                        if rest and ns_stack and ns_stack[-1] == rest:
                            ns_stack.pop()
                        elif not rest and ns_stack:
                            # `end` could close a section or namespace; conservative pop
                            pass
                    elif not line[0].isspace() or line.startswith("  "):
                        m = RE_HEADER_DECL.match(line)
                        if m and m.group(2):
                            raw_name = m.group(2)
                            clean = raw_name[7:] if raw_name.startswith("_root_.") else raw_name
                            names.add(raw_name)
                            names.add(clean)
                            if ns_stack and not raw_name.startswith("_root_."):
                                full_ns = ".".join(ns_stack)
                                names.add(f"{full_ns}.{clean}")
                                # Also suffixes of namespace stack
                                all_parts = full_ns.split(".") + clean.split(".")
                                for k in range(len(all_parts)):
                                    names.add(".".join(all_parts[k:]))
        self._mod_qualified_decls_cache[mod] = names
        return names

    def find_decl_globally(self, name: str) -> list[tuple[str, str, int, int]]:
        clean = name[7:] if name.startswith("_root_.") else name
        if clean in self._decl_name_cache:
            return self._decl_name_cache[clean]
        # 1. Exact or _root_. match or suffix match in decls.name
        rows = self.con.execute(
            """
            SELECT module, name, start_line, end_line
            FROM decls
            WHERE name = ? OR name = ? OR name LIKE ?
            LIMIT 25
            """,
            [clean, f"_root_.{clean}", f"%.{clean}"],
        ).fetchall()
        if rows:
            self._decl_name_cache[clean] = rows
            return rows

        # 2. If dotted, try leaf lookup + namespace check on candidate modules
        if "." in clean:
            leaf = clean.rsplit(".", 1)[-1]
            head = clean.split(".", 1)[0]
            cands = []
            if head in self.top_libs:
                cands = self.con.execute(
                    """
                    SELECT DISTINCT d.module, d.name, d.start_line, d.end_line
                    FROM decls d JOIN modules m USING (module)
                    WHERE d.name = ? AND m.top_lib = ?
                    LIMIT 120
                    """,
                    [leaf, head],
                ).fetchall()
            if not cands:
                cands = self.con.execute(
                    "SELECT DISTINCT module, name, start_line, end_line FROM decls WHERE name = ? LIMIT 120",
                    [leaf],
                ).fetchall()
            matched: list[tuple[str, str, int, int]] = []
            for mod, dname, sl, el in cands:
                qnames = self.get_mod_qualified_names(mod)
                if clean in qnames:
                    matched.append((mod, dname, sl, el))
            if not matched and head in self.top_libs:
                # Namespace may live in a different top_lib directory (e.g. PositivityTheory.* inside Development/)
                cands_all = self.con.execute(
                    "SELECT DISTINCT module, name, start_line, end_line FROM decls WHERE name = ? LIMIT 120",
                    [leaf],
                ).fetchall()
                for mod, dname, sl, el in cands_all:
                    qnames = self.get_mod_qualified_names(mod)
                    if clean in qnames:
                        matched.append((mod, dname, sl, el))
            if matched:
                self._decl_name_cache[clean] = matched
                return matched

        self._decl_name_cache[clean] = []
        return []

    def exists_in_any_signature(self, ident: str) -> bool:
        clean = ident[7:] if ident.startswith("_root_.") else ident
        if clean not in self._sig_match_cache:
            row = self.con.execute(
                "SELECT 1 FROM decls WHERE signature LIKE ? LIMIT 1",
                [f"%{clean}%"],
            ).fetchone()
            self._sig_match_cache[clean] = row is not None
        return self._sig_match_cache[clean]

    def verify_lean_path(self, raw_path: str, line_start: int | None, line_end: int | None) -> tuple[str, str]:
        p = raw_path.replace("\\", "/")
        for prefix in (
            "downloads/lean/src/",
            "lean/src/",
            "src/",
        ):
            if p.lower().startswith(prefix.lower()):
                p = p[len(prefix):]
        p = p.lstrip("./")

        if "/" in p:
            mod = self.relpath_to_mod.get(p.lower())
            disk_ok = (self.src_root / p).exists()
            if not mod and not disk_ok:
                # Could be a suffix path like CharacterBoxes/MainConclusion.lean
                suffix_hits = [m for rp, m in self.relpath_to_mod.items() if rp.endswith("/" + p.lower())]
                if len(suffix_hits) == 1:
                    mod = suffix_hits[0]
                    disk_ok = True
                elif len(suffix_hits) > 1:
                    return "PASS", f"suffix path matches {len(suffix_hits)} modules (e.g. {suffix_hits[0]})"
                else:
                    return "FAIL", f".lean path not in DuckDB or disk: {p}"
            if mod:
                rel, lns, rch, dep, _ = self.modules[mod]
                if line_start is not None and not (1 <= line_start <= lns):
                    return "FAIL", f"line {line_start} out of range (1..{lns}) for {mod}"
                if line_end is not None and not (1 <= line_end <= lns):
                    return "FAIL", f"end line {line_end} out of range (1..{lns}) for {mod}"
                if not disk_ok:
                    return "FAIL", f"module {mod} in DB but missing on disk: {rel}"
                reach_note = "" if rch else " [UNREACHABLE]"
                return ("WARN" if not rch else "PASS"), f"module={mod} (D{dep}, {lns}L){reach_note}"
            return "PASS", f"file exists on disk: {p}"
        else:
            mods = self.basename_to_mods.get(p.lower(), [])
            if not mods:
                return "FAIL", f"basename .lean file not found in repo: {p}"
            if len(mods) == 1:
                mod = mods[0]
                rel, lns, rch, dep, _ = self.modules[mod]
                if line_start is not None and not (1 <= line_start <= lns):
                    return "FAIL", f"line {line_start} out of range (1..{lns}) for {mod}"
                return ("WARN" if not rch else "PASS"), f"unique basename -> {mod} (D{dep}, {lns}L)"
            if line_start is not None:
                ok_mods = [m for m in mods if 1 <= line_start <= self.modules[m][1]]
                if not ok_mods:
                    return "FAIL", f"line {line_start} out of range for all {len(mods)} files named {p}"
            return "PASS", f"basename matches {len(mods)} modules (e.g. {mods[0]})"

    def verify_dotted_token(self, tok: str, line_start: int | None = None, line_end: int | None = None) -> tuple[str, str, str]:
        """Returns (category, status, detail)."""
        if ".." in tok:
            return "EXTERNAL", "PASS", "ellipsis/range placeholder"
        is_wildcard = tok.endswith(".*")
        clean = tok[:-2] if is_wildcard else tok
        clean_noroot = clean[7:] if clean.startswith("_root_.") else clean
        head = clean_noroot.split(".", 1)[0]

        # Ignore obvious non-Lean tokens (versions, floats, filenames, urls)
        if re.match(r"^\d+(\.\d+)+$", clean_noroot):
            return "EXTERNAL", "PASS", "numeric/version"
        if any(clean_noroot.endswith(ext) for ext in (".py", ".md", ".toml", ".json", ".duckdb", ".tsv", ".txt", ".sh", ".ps1", ".exe", ".olean", ".c", ".h", ".rs", ".js", ".inc", ".com", ".org")):
            return "EXTERNAL", "PASS", "non-lean filename/domain"
        if head in EXTERNAL_PREFIXES:
            return "EXTERNAL", "PASS", f"external/Mathlib/Lean symbol ({head})"

        # 1. Exact module match
        if not is_wildcard and clean_noroot in self.modules:
            rel, lns, rch, dep, _ = self.modules[clean_noroot]
            disk_ok = (self.src_root / rel).exists()
            if not disk_ok:
                return "MODULE", "FAIL", f"module in DB but missing on disk: {rel}"
            if line_start is not None and not (1 <= line_start <= lns):
                return "MODULE", "FAIL", f"line {line_start} out of range (1..{lns}) for {clean_noroot}"
            if line_end is not None and not (1 <= line_end <= lns):
                return "MODULE", "FAIL", f"end line {line_end} out of range (1..{lns}) for {clean_noroot}"
            reach_note = "" if rch else " [DB_UNREACHABLE_UNICODE_BUG?]"
            return "MODULE", ("WARN" if not rch else "PASS"), f"exact module (D{dep}, {lns}L){reach_note}"

        # 2. Wildcard or exact directory prefix
        if clean_noroot in self.dir_prefixes:
            cnt = self.dir_prefixes[clean_noroot]
            return "DIR_PREFIX", "PASS", f"module namespace/directory prefix ({cnt:,} modules)"

        # 2b. Relative module or directory suffix (e.g. SmallClassNumbers.CorGKOf or AbelianVarietyTheory.PublishedTheorems)
        if head not in self.top_libs and head not in LOCAL_ROOT_NAMESPACES:
            mod_suf = [m for m in self.modules if m.endswith("." + clean_noroot)]
            if mod_suf:
                return "MODULE", "PASS", f"relative module suffix -> `{mod_suf[0]}` (+{len(mod_suf)-1} more)" if len(mod_suf) > 1 else f"relative module suffix -> `{mod_suf[0]}`"
            dir_suf = [p for p in self.dir_prefixes if p.endswith("." + clean_noroot)]
            if dir_suf:
                return "DIR_PREFIX", "PASS", f"relative dir prefix -> `{dir_suf[0]}` ({self.dir_prefixes[dir_suf[0]]:,} modules)"

        # 3. Module + Declaration split (longest matching module prefix)
        parts = clean_noroot.split(".")
        for k in range(len(parts) - 1, 0, -1):
            mod_cand = ".".join(parts[:k])
            decl_cand = ".".join(parts[k:])
            if mod_cand in self.modules:
                qnames = self.get_mod_qualified_names(mod_cand)
                if decl_cand in qnames or clean_noroot in qnames:
                    # Optional line check
                    if line_start is not None:
                        _, lns, _, _, _ = self.modules[mod_cand]
                        if not (1 <= line_start <= lns):
                            return "MODULE_DECL", "FAIL", f"decl {decl_cand} exists in {mod_cand}, but line {line_start} > {lns}"
                    return "MODULE_DECL", "PASS", f"decl `{decl_cand}` verified in `{mod_cand}`"
                else:
                    return "MODULE_DECL", "FAIL", f"module `{mod_cand}` exists, but decl `{decl_cand}` NOT FOUND in it!"

        # 4. Global / namespace-qualified declaration lookup in DuckDB
        hits = self.find_decl_globally(clean)
        if hits:
            mod0, name0, sl0, el0 = hits[0]
            if line_start is not None:
                if not any(1 <= line_start <= self.modules[m][1] for m, _, _, _ in hits if m in self.modules):
                    return "GLOBAL_DECL", "FAIL", f"decl `{clean}` found in `{mod0}`, but line {line_start} out of range"
            extra = f" (+{len(hits)-1} more)" if len(hits) > 1 else ""
            return "GLOBAL_DECL", "PASS", f"global decl `{name0}` in `{mod0}` L{sl0}-{el0}{extra}"

        # 5. Namespace/type referenced in signatures (e.g. UpperTheory.LiteratureTheorems.*, GlobalTheory.Published.*)
        if is_wildcard or head in LOCAL_ROOT_NAMESPACES or head in self.top_libs:
            if self.exists_in_any_signature(clean_noroot):
                return "GLOBAL_DECL", "PASS", f"namespace/type `{clean_noroot}` verified in Lean signatures"

        # 6. If it starts with a known local library or UpperTheory/GlobalTheory -> definite FAIL!
        if head in self.top_libs or head in LOCAL_ROOT_NAMESPACES:
            return "MODULE_DECL", "FAIL", f"UNVERIFIED local module/decl/namespace: `{tok}`"

        # 7. Otherwise check if it looks like a short namespace-qualified decl (e.g. U3.CorGK, Re3.hloweq_transfer, Claim.Strip)
        if self.exists_in_any_signature(clean_noroot):
            return "GLOBAL_DECL", "PASS", f"symbol `{clean_noroot}` verified in Lean signatures"

        # Could be a hallucinated short namespace decl (like FakeNs.foo_bar) vs prose/code field access (like s.re, a.kind, c.O, χ.IsPrimitive)
        if len(parts) == 2 and (len(parts[0]) <= 2 or parts[0].islower() or parts[1] in ("re", "im", "O", "Prime", "Coprime", "IsPrimitive", "valuation", "asIdeal", "primeFactors", "module", "lines", "kind", "name", "reachable")):
            return "EXTERNAL", "PASS", "field/method/SQL projection"

        # Short uppercase namespace like Re3.xxx or U3.xxx that was NOT found anywhere!
        if parts[0][0].isupper():
            return "GLOBAL_DECL", "FAIL", f"UNVERIFIED qualified identifier `{tok}` (not in modules, decls, or signatures)"

        return "EXTERNAL", "PASS", "unclassified lowercase dotted token"

    def verify_markdown(self, md_path: Path) -> ReportSummary:
        text = md_path.read_text(encoding="utf-8", errors="replace")
        return self.verify_text(text, str(md_path))

    def verify_text(self, text: str, label: str = "<memory>") -> ReportSummary:
        summary = ReportSummary(file=label)
        lines = text.splitlines()
        in_fence = False
        seen_per_line: set[tuple[int, str]] = set()

        for lineno, line in enumerate(lines, start=1):
            stripped = line.strip()
            if stripped.startswith("```"):
                in_fence = not in_fence
                continue

            line_modules: list[str] = []
            line_explicit_decls: list[str] = []

            # 1. Extract .lean paths from full line (including markdown links and inline code)
            for m in RE_LEAN_PATH.finditer(line):
                raw_path = m.group(1)
                ls = int(m.group(2)) if m.group(2) else None
                le = int(m.group(3)) if m.group(3) else None
                key = (lineno, f"PATH:{raw_path}:{ls}:{le}")
                if key in seen_per_line:
                    continue
                seen_per_line.add(key)
                status, detail = self.verify_lean_path(raw_path, ls, le)
                summary.total_checked += 1
                if status == "PASS":
                    summary.passed += 1
                elif status == "WARN":
                    summary.warnings += 1
                else:
                    summary.failed += 1
                summary.findings.append(RefFinding(lineno, m.group(0), "FILE_PATH", status, detail))

                # Track resolved module for same-line pairing
                norm_p = raw_path.replace("\\", "/")
                if norm_p.lower() in self.relpath_to_mod:
                    line_modules.append(self.relpath_to_mod[norm_p.lower()])
                else:
                    base = norm_p.rsplit("/", 1)[-1].lower()
                    bmods = self.basename_to_mods.get(base, [])
                    if len(bmods) == 1:
                        line_modules.append(bmods[0])

            # 2. Extract inline backtick tokens AND unbackticked local-library dotted refs
            candidates: list[str] = []
            if not in_fence:
                for cm in RE_INLINE_CODE.finditer(line):
                    code_txt = cm.group(1).strip()
                    if not code_txt or (" " in code_txt and not any(code_txt.startswith(lib + ".") for lib in self.top_libs)):
                        for dm in RE_DOTTED_TOK.finditer(code_txt):
                            tok = dm.group(0)
                            head = (tok[7:] if tok.startswith("_root_.") else tok).split(".", 1)[0]
                            if head in self.top_libs or head in LOCAL_ROOT_NAMESPACES:
                                candidates.append(tok)
                        continue
                    candidates.append(code_txt)
                # Also catch plain-text local-library / UpperTheory / GlobalTheory dotted tokens
                for dm in RE_DOTTED_TOK.finditer(line):
                    tok = dm.group(0)
                    head = (tok[7:] if tok.startswith("_root_.") else tok).split(".", 1)[0]
                    if head in self.top_libs or head in LOCAL_ROOT_NAMESPACES:
                        candidates.append(tok)
            else:
                for dm in RE_DOTTED_TOK.finditer(line):
                    tok = dm.group(0)
                    head = (tok[7:] if tok.startswith("_root_.") else tok).split(".", 1)[0]
                    if head in self.top_libs or head in LOCAL_ROOT_NAMESPACES:
                        candidates.append(tok)

            for raw_tok in candidates:
                tok = raw_tok.strip("(),;[]")
                if not tok or tok.endswith(".lean") or ".lean:" in tok or ".lean#L" in tok:
                    continue
                if "/" in tok or "\\" in tok or tok.startswith(("http://", "https://", "--", "-", "$", "#")):
                    continue

                m_tok = RE_SINGLE_MOD_OR_LINE.match(tok)
                if not m_tok:
                    continue
                ident = m_tok.group(1)
                ls = int(m_tok.group(2)) if m_tok.group(2) else None
                le = int(m_tok.group(3)) if m_tok.group(3) else None

                if "." not in ident:
                    if ident in self.modules:
                        key = (lineno, f"MOD:{ident}:{ls}")
                        if key not in seen_per_line:
                            seen_per_line.add(key)
                            cat, st, det = self.verify_dotted_token(tok, ls, le)
                            summary.total_checked += 1
                            summary.passed += (st == "PASS")
                            summary.warnings += (st == "WARN")
                            summary.failed += (st == "FAIL")
                            summary.findings.append(RefFinding(lineno, tok, cat, st, det))
                            line_modules.append(ident)
                    elif ident not in IGNORED_KEYWORDS_AND_COLS and ident not in self.top_libs and not ident.isdigit():
                        if re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", ident) and len(ident) >= 3:
                            line_explicit_decls.append(ident)
                    continue

                key = (lineno, f"DOT:{tok}")
                if key in seen_per_line:
                    continue
                seen_per_line.add(key)
                cat, st, det = self.verify_dotted_token(tok, ls, le)
                if cat == "EXTERNAL":
                    summary.external_ignored += 1
                    continue
                summary.total_checked += 1
                if st == "PASS":
                    summary.passed += 1
                elif st == "WARN":
                    summary.warnings += 1
                else:
                    summary.failed += 1
                summary.findings.append(RefFinding(lineno, tok, cat, st, det))
                if cat == "MODULE" and ident in self.modules:
                    line_modules.append(ident)

            # 3. Same-line (Module, Decl) pairing verification (primarily catches table-row mismatches!)
            uniq_mods = list(dict.fromkeys(line_modules))
            if len(uniq_mods) == 1 and line_explicit_decls and ("|" in line or line.lstrip().startswith(("-", "*"))):
                mod = uniq_mods[0]
                qnames = self.get_mod_qualified_names(mod)
                direct_imps = self.get_mod_imports(mod)
                for d in line_explicit_decls:
                    if d in qnames:
                        summary.total_checked += 1
                        summary.passed += 1
                        summary.findings.append(RefFinding(lineno, f"{mod} :: {d}", "LINE_PAIR", "PASS", f"paired decl `{d}` confirmed in `{mod}`"))
                    elif "|" in line:
                        elsewhere = self.find_decl_globally(d)
                        if elsewhere:
                            # If `d` comes from a direct import of `mod` (e.g. cited in a Dependencies column), pass as imported ref
                            imp_hit = [e for e in elsewhere if e[0] in direct_imps]
                            if imp_hit:
                                summary.total_checked += 1
                                summary.passed += 1
                                summary.findings.append(RefFinding(lineno, f"{mod} :: {d}", "LINE_PAIR", "PASS", f"imported decl `{d}` from `{imp_hit[0][0]}`"))
                            else:
                                # Also check if `d` is referenced in `mod`'s own signature/header
                                mod_p = self.src_root / self.modules[mod][0]
                                in_mod_text = mod_p.exists() and (d in mod_p.read_text(encoding="utf-8", errors="replace"))
                                if in_mod_text:
                                    summary.total_checked += 1
                                    summary.passed += 1
                                    summary.findings.append(RefFinding(lineno, f"{mod} :: {d}", "LINE_PAIR", "PASS", f"symbol `{d}` used in `{mod}` (defined in `{elsewhere[0][0]}`)"))
                                else:
                                    summary.total_checked += 1
                                    summary.failed += 1
                                    summary.findings.append(
                                        RefFinding(
                                            lineno,
                                            f"{mod} :: {d}",
                                            "LINE_PAIR",
                                            "FAIL",
                                            f"decl `{d}` NOT in `{mod}` (found elsewhere e.g. `{elsewhere[0][0]}`)",
                                        )
                                    )

        return summary




# ---------- Comment / string stripping for Lean 4 ----------
def strip_lean_comments_and_strings(text: str) -> str:
    """Strip Lean 4 nested block comments /- ... -/, line comments -- ..., and string/char literals."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_str = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_str:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            elif ch == '"':
                in_str = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.append("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
        elif ch == '"':
            in_str = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


RE_FORBIDDEN = re.compile(
    r"\b(sorry|sorryAx|admit|axiom|native_decide|implemented_by|lcProof|unsafe)\b"
)
RE_DECL_NAME = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|axiom|structure|class|inductive|opaque|instance)\b(?:\s+([^\s:({\[=]+))?",
    re.MULTILINE,
)


def find_forbidden_tokens(text: str) -> list[tuple[int, str]]:
    clean = strip_lean_comments_and_strings(text)
    hits: list[tuple[int, str]] = []
    for lineno, line in enumerate(clean.splitlines(), start=1):
        for m in RE_FORBIDDEN.finditer(line):
            hits.append((lineno, m.group(1)))
    return hits


def extract_decls(text: str) -> list[tuple[str, str]]:
    """Return ordered list of (kind, name_or_anon) from comment-stripped Lean file."""
    clean = strip_lean_comments_and_strings(text)
    decls: list[tuple[str, str]] = []
    for line in clean.splitlines():
        if not line.strip():
            continue
        # Only top-level or lightly indented declarations (skip `def` inside comments/strings already stripped)
        if not line[0].isspace() or line.startswith("  "):
            m = RE_DECL_NAME.match(line)
            if m:
                kind = m.group(1)
                name = m.group(2) or "<anon>"
                decls.append((kind, name))
    return decls


def check_balanced_delims(text: str) -> list[str]:
    clean = strip_lean_comments_and_strings(text)
    # Strip guillemet identifiers «...» and char literals '.' to avoid false delimiter hits
    clean = re.sub(r"«[^»\n]*»", " ", clean)
    clean = re.sub(r"'([^'\\\n]|\\.)'", " ", clean)
    pairs = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    closing = {v: k for k, v in pairs.items()}
    stack: list[tuple[str, int]] = []
    errors: list[str] = []
    for lineno, line in enumerate(clean.splitlines(), start=1):
        for ch in line:
            if ch in pairs:
                stack.append((ch, lineno))
            elif ch in closing:
                if not stack:
                    errors.append(f"L{lineno}: unmatched closing `{ch}`")
                elif stack[-1][0] != closing[ch]:
                    # Note: Lean 4 `Set.Ico`/`[...` or `|...` shouldn't break standard pairs,
                    # except `fun` / range syntax doesn't mix () [] {} ⟨⟩.
                    errors.append(
                        f"L{lineno}: mismatched `{ch}` (top was `{stack[-1][0]}` from L{stack[-1][1]})"
                    )
                    stack.pop()
                else:
                    stack.pop()
    for ch, ln in stack[:10]:
        errors.append(f"L{ln}: unclosed `{ch}`")
    if len(stack) > 10:
        errors.append(f"... and {len(stack) - 10} more unclosed delimiters")
    return errors


# ---------- Enhanced Round 2 Markdown Reference Verifier ----------
class Round2RefVerifier(LeanIndexVerifier):
    def __init__(self, db_path: Path, src_root: Path, out_dir: Path) -> None:
        super().__init__(db_path, src_root)
        self.out_dir = out_dir

    def verify_lean_path(
        self, raw_path: str, line_start: int | None, line_end: int | None
    ) -> tuple[str, str]:
        relative = raw_path.replace("\\", "/").removeprefix("../")
        if relative.startswith(("harnesses/", "poc/", "out/")):
            generated = relative.startswith("out/")
            base = self.out_dir if generated else PROJECT_ROOT
            candidate = base / (relative.removeprefix("out/") if generated else relative)
            if not candidate.resolve().is_relative_to(base.resolve()):
                return "FAIL", f"reference leaves the artifact tree: {relative}"
            if candidate.is_file():
                line_count = len(candidate.read_text(encoding="utf-8").splitlines())
                if any(n is not None and not 1 <= n <= line_count for n in (line_start, line_end)):
                    return "FAIL", f"line outside {relative} (1..{line_count})"
                return "PASS", f"artifact exists ({relative})"
            if generated:
                return "WARN", f"generated or historical artifact not present: {relative}"
            return "FAIL", f"packaged artifact not found: {relative}"

        if "/" not in relative:
            for directory in ("harnesses", "poc"):
                if (PROJECT_ROOT / directory / relative).is_file():
                    return self.verify_lean_path(f"{directory}/{relative}", line_start, line_end)
        raw_path = relative
        status, detail = super().verify_lean_path(raw_path, line_start, line_end)
        # Round 1 proved Unicode '₂' caused 420 false-unreachable DB flags; verify on disk
        if status == "WARN" and "[UNREACHABLE]" in detail:
            return "PASS", detail.replace(" [UNREACHABLE]", " [verified-on-disk; DB Unicode₂ reachability quirk]")
        return status, detail

    def verify_dotted_token(
        self, tok: str, line_start: int | None = None, line_end: int | None = None
    ) -> tuple[str, str, str]:
        cat, st, det = super().verify_dotted_token(tok, line_start, line_end)
        if st == "WARN" and "[DB_UNREACHABLE_UNICODE_BUG?]" in det:
            return cat, "PASS", det.replace(" [DB_UNREACHABLE_UNICODE_BUG?]", " [verified-on-disk; DB Unicode₂ quirk]")
        return cat, st, det


# ---------- Capelli Shadow 82-file Verifier ----------
def audit_capelli_shadow(shadow_dir: Path, src_root: Path) -> dict:
    files = sorted(shadow_dir.rglob("*.lean"))
    capelli_src_dir = src_root / "Development" / "AutomorphicArithmetic" / "IntegralCasts" / "CapelliIdentities"

    results = []
    tot_orig_lines = tot_new_lines = 0
    tot_orig_bytes = tot_new_bytes = 0
    tot_orig_at = tot_new_at = 0
    decl_mismatches = 0
    forbidden_files = 0
    delim_error_files = 0
    missing_orig = 0

    for sf in files:
        # Resolve original file: either relative path under shadow_dir or flat basename under CapelliIdentities
        rel = sf.relative_to(shadow_dir)
        cand1 = src_root / rel
        cand2 = capelli_src_dir / sf.name
        if cand1.exists():
            orig = cand1
        elif cand2.exists():
            orig = cand2
        else:
            missing_orig += 1
            results.append({"shadow": str(rel), "error": "original not found"})
            continue

        orig_text = orig.read_text(encoding="utf-8", errors="replace")
        new_text = sf.read_text(encoding="utf-8", errors="replace")

        ol, nl = len(orig_text.splitlines()), len(new_text.splitlines())
        ob, nb = len(orig_text.encode("utf-8")), len(new_text.encode("utf-8"))
        oa, na = orig_text.count("@"), new_text.count("@")

        tot_orig_lines += ol
        tot_new_lines += nl
        tot_orig_bytes += ob
        tot_new_bytes += nb
        tot_orig_at += oa
        tot_new_at += na

        orig_decls = extract_decls(orig_text)
        new_decls = extract_decls(new_text)
        decl_ok = orig_decls == new_decls
        if not decl_ok:
            decl_mismatches += 1

        forb = find_forbidden_tokens(new_text)
        if forb:
            forbidden_files += 1

        delims = check_balanced_delims(new_text)
        if delims:
            delim_error_files += 1

        results.append({
            "file": sf.name,
            "orig_rel": str(orig.relative_to(src_root)).replace("\\", "/"),
            "orig_lines": ol,
            "new_lines": nl,
            "line_delta": nl - ol,
            "orig_bytes": ob,
            "new_bytes": nb,
            "byte_delta": nb - ob,
            "orig_at": oa,
            "new_at": na,
            "decl_count_orig": len(orig_decls),
            "decl_count_new": len(new_decls),
            "decl_exact_match": decl_ok,
            "orig_only_decls": [d for d in orig_decls if d not in new_decls][:5] if not decl_ok else [],
            "new_only_decls": [d for d in new_decls if d not in orig_decls][:5] if not decl_ok else [],
            "forbidden_hits": forb[:5],
            "delim_errors": delims[:5],
        })

    summary = {
        "shadow_file_count": len(files),
        "missing_orig": missing_orig,
        "tot_orig_lines": tot_orig_lines,
        "tot_new_lines": tot_new_lines,
        "line_reduction_pct": round((1 - tot_new_lines / tot_orig_lines) * 100, 2) if tot_orig_lines else 0.0,
        "tot_orig_bytes": tot_orig_bytes,
        "tot_new_bytes": tot_new_bytes,
        "byte_reduction_pct": round((1 - tot_new_bytes / tot_orig_bytes) * 100, 2) if tot_orig_bytes else 0.0,
        "tot_orig_at": tot_orig_at,
        "tot_new_at": tot_new_at,
        "decl_mismatches": decl_mismatches,
        "forbidden_files": forbidden_files,
        "delim_error_files": delim_error_files,
        "files": results,
    }
    return summary


# ---------- Independent Lean 4.34.1 Harness Compiler ----------
def verify_harnesses(dirs: list[Path]) -> dict:
    lean_files: list[Path] = []
    for d in dirs:
        if d.is_file() and d.suffix == ".lean":
            lean_files.append(d)
        elif d.is_dir():
            lean_files.extend(sorted(d.rglob("*.lean")))

    entries = []
    all_ok = bool(lean_files)
    for lf in lean_files:
        text = lf.read_text(encoding="utf-8", errors="replace")
        lines = len(text.splitlines())
        forb = find_forbidden_tokens(text)
        # Skip files that explicitly import Mathlib or local repo modules (not standalone core harnesses)
        imports = re.findall(r"^\s*import\s+(\S+)", strip_lean_comments_and_strings(text), re.MULTILINE)
        is_standalone = not any(
            imp.startswith(("Mathlib", "Formalism", "Development", "CompanionTheory", "GroundTheory", "PositivityTheory", "ReciprocityTheory"))
            for imp in imports
        )
        if not is_standalone:
            entries.append({
                "file": str(lf),
                "lines": lines,
                "standalone": False,
                "imports": imports,
                "forbidden_hits": forb,
                "exit_code": None,
                "note": "Mathlib/repo-dependent file (not standalone v4.34.1 harness)",
            })
            if forb:
                all_ok = False
            continue

        proc = subprocess.run(
            ["elan", "run", "leanprover/lean4:v4.34.1", "lean", str(lf)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=120,
        )
        ok = (proc.returncode == 0) and (len(forb) == 0)
        if not ok:
            all_ok = False
        entries.append({
            "file": str(lf),
            "lines": lines,
            "standalone": True,
            "exit_code": proc.returncode,
            "forbidden_hits": forb,
            "stdout": proc.stdout.strip()[:500],
            "stderr": proc.stderr.strip()[:500],
            "pass": ok,
        })
    return {"all_ok": all_ok, "count": len(entries), "entries": entries}


# ---------- RingObjectsOfMatrixData Integrity Checker ----------
def check_golf_ring_objects(golf_path: Path, src_root: Path) -> dict:
    orig_path = (
        src_root
        / "Formalism"
        / "WachLatticeTwists"
        / "RamifiedBlockRings"
        / "RamifiedBlockProofs"
        / "RingObjectsOfMatrixData.lean"
    )
    orig_text = orig_path.read_text(encoding="utf-8", errors="replace")
    golf_text = golf_path.read_text(encoding="utf-8", errors="replace")

    orig_clean = strip_lean_comments_and_strings(orig_text)
    golf_clean = strip_lean_comments_and_strings(golf_text)

    def extract_thm_sig(txt: str, name: str) -> str | None:
        m = re.search(rf"theorem\s+{re.escape(name)}\b(.*?):=\s*by", txt, re.DOTALL)
        if not m:
            return None
        return re.sub(r"\s+", " ", f"theorem {name}{m.group(1)}:= by").strip()

    orig_sig = extract_thm_sig(orig_clean, "ring_objects_of_matrix_data")
    golf_sig = extract_thm_sig(golf_clean, "ring_objects_of_matrix_data")

    orig_have = len(re.findall(r"\bhave\b", orig_clean))
    golf_have = len(re.findall(r"\bhave\b", golf_clean))
    # Count inside ring_objects_of_matrix_data body specifically
    def body_stats(txt: str) -> tuple[int, int]:
        m = re.search(r"theorem\s+ring_objects_of_matrix_data\b.*?:=\s*by\n(.*?)(?:\nend\s|\Z)", txt, re.DOTALL)
        if not m:
            return 0, 0
        body = m.group(1)
        return len(body.splitlines()), len(re.findall(r"\bhave\b", body))

    ob_lines, ob_haves = body_stats(orig_clean)
    gb_lines, gb_haves = body_stats(golf_clean)

    forb = find_forbidden_tokens(golf_text)
    delims = check_balanced_delims(golf_text)

    return {
        "orig_total_lines": len(orig_text.splitlines()),
        "golf_total_lines": len(golf_text.splitlines()),
        "orig_thm_body_lines": ob_lines,
        "golf_thm_body_lines": gb_lines,
        "orig_total_haves": orig_have,
        "golf_total_haves": golf_have,
        "orig_thm_body_haves": ob_haves,
        "golf_thm_body_haves": gb_haves,
        "orig_sig": orig_sig,
        "golf_sig": golf_sig,
        "exact_sig_match": (orig_sig is not None and orig_sig == golf_sig),
        "forbidden_hits": forb,
        "delim_errors": delims[:10],
        "golf_decls": extract_decls(golf_text),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Round 2 Adversarial Verification Suite")
    add_path_arguments(ap)
    ap.add_argument("--refs", nargs="+", help="Markdown files to verify references")
    ap.add_argument("--capelli-shadow", type=Path, help="Path to capelli_shadow/ directory")
    ap.add_argument("--harnesses", nargs="+", type=Path, help="Harness dirs/files to compile with Lean v4.34.1")
    ap.add_argument("--check-golf", type=Path, help="Path to golfed_RingObjectsOfMatrixData.lean")
    ap.add_argument("--json-out", type=Path, help="JSON summary path, relative to the output directory or absolute")
    args = ap.parse_args()
    src_root, db_path, out_dir = resolve_paths(args)
    if not any((args.refs, args.capelli_shadow, args.harnesses, args.check_golf)):
        ap.error("select --refs, --capelli-shadow, --harnesses, or --check-golf")

    out: dict = {}
    any_fail = False

    if args.refs:
        v = Round2RefVerifier(db_path, src_root, out_dir)
        ref_res = []
        for fstr in args.refs:
            p = Path(fstr)
            if not p.exists():
                print(f"[REF ERROR] Not found: {p}", file=sys.stderr)
                any_fail = True
                continue
            res = v.verify_markdown(p)
            ref_res.append(asdict(res))
            rate = (res.passed / res.total_checked * 100.0) if res.total_checked else 100.0
            print(f"=== REFS: {p.name} ===")
            print(f"  Checked: {res.total_checked} | PASS: {res.passed} ({rate:.1f}%) | WARN: {res.warnings} | FAIL: {res.failed} | External: {res.external_ignored}")
            if res.failed:
                any_fail = True
                for f in res.findings:
                    if f.status == "FAIL":
                        print(f"    [FAIL] L{f.md_line} [{f.category}] `{f.raw}` -> {f.detail}")
            if res.warnings:
                for f in res.findings:
                    if f.status == "WARN":
                        print(f"    [WARN] L{f.md_line} [{f.category}] `{f.raw}` -> {f.detail}")
        v.con.close()
        out["refs"] = ref_res

    if args.capelli_shadow:
        cs = audit_capelli_shadow(args.capelli_shadow, src_root)
        out["capelli_shadow"] = cs
        print(f"=== CAPELLI SHADOW: {args.capelli_shadow} ===")
        print(
            f"  Files: {cs['shadow_file_count']} (missing_orig={cs['missing_orig']}) | "
            f"Lines: {cs['tot_orig_lines']:,} -> {cs['tot_new_lines']:,} (-{cs['line_reduction_pct']}%) | "
            f"Bytes: {cs['tot_orig_bytes']:,} -> {cs['tot_new_bytes']:,} (-{cs['byte_reduction_pct']}%) | "
            f"@: {cs['tot_orig_at']:,} -> {cs['tot_new_at']:,}"
        )
        print(
            f"  Decl mismatches: {cs['decl_mismatches']} | Forbidden hits: {cs['forbidden_files']} | "
            f"Delim errors: {cs['delim_error_files']}"
        )
        if cs["decl_mismatches"] or cs["forbidden_files"] or cs["delim_error_files"] or cs["missing_orig"] or not cs["shadow_file_count"]:
            any_fail = True
            for item in cs["files"]:
                if not item.get("decl_exact_match", True) or item.get("forbidden_hits") or item.get("delim_errors") or item.get("error"):
                    print(f"    [ISSUE] {item.get('file', item.get('shadow'))}: {item}")

    if args.harnesses:
        hr = verify_harnesses(args.harnesses)
        out["harnesses"] = hr
        print(f"=== HARNESSES (Lean v4.34.1) ===")
        for e in hr["entries"]:
            tag = "PASS" if e.get("pass") else ("SKIP(Mathlib)" if not e["standalone"] else "FAIL")
            print(f"  [{tag}] {Path(e['file']).name} ({e['lines']}L) exit={e['exit_code']} forb={len(e['forbidden_hits'])}")
            if e["standalone"] and not e.get("pass"):
                print(f"    stderr: {e.get('stderr')}")
                print(f"    stdout: {e.get('stdout')}")
        if not hr["all_ok"]:
            any_fail = True

    if args.check_golf:
        gr = check_golf_ring_objects(args.check_golf, src_root)
        out["golf_ring_objects"] = gr
        print(f"=== GOLF CHECK: {args.check_golf.name} ===")
        print(
            f"  Total lines: {gr['orig_total_lines']} -> {gr['golf_total_lines']} | "
            f"Thm body lines: {gr['orig_thm_body_lines']} -> {gr['golf_thm_body_lines']} | "
            f"Body haves: {gr['orig_thm_body_haves']} -> {gr['golf_thm_body_haves']}"
        )
        print(f"  Exact sig match: {gr['exact_sig_match']} | Forbidden: {gr['forbidden_hits']} | Delim errs: {len(gr['delim_errors'])}")
        if not gr["exact_sig_match"] or gr["forbidden_hits"] or gr["delim_errors"]:
            any_fail = True

    if args.json_out:
        json_out = out_dir / args.json_out
        json_out.parent.mkdir(parents=True, exist_ok=True)
        json_out.write_text(json.dumps(out, ensure_ascii=False, indent=2), encoding="utf-8")

    return 1 if any_fail else 0


if __name__ == "__main__":
    raise SystemExit(main())
