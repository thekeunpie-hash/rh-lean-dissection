#!/usr/bin/env python3
"""
Standalone Lean 4 Stub Generator (`make_stub.py`) for Track C Proof-Golfing Sandbox.

Usage:
  python make_stub.py --module <Mod> --decl <DeclName> --out <out.lean> [--mode mathlib|pure-core]

Reads `lean_index.duckdb` + the target `.lean` file and its direct/2-hop imports' signatures:
  1. Extracts the target declaration + transitively referenced local defs/structures/theorems
     from the same module (preserving source order, handling universe-polymorphic `Foo.{u}` names).
  2. Detects external identifiers referenced from imported local modules (avoiding binder false
     positives) and resolves them against `lean_index.duckdb` (`decls` + `imports`).
  3. Emits minimal `opaque` / `axiom` stubs with provenance comments for external project deps.
  4. Produces a clean standalone `.lean` sandbox file with metadata header (original line count,
     sig/body split, explicit-@ count, local deps, external stubs, exact toolchain verification cmds).
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from index_lean import add_path_arguments, resolve_paths, DEFAULT_INDEX_DB, DEFAULT_SRC_ROOT


RE_IDENT = re.compile(r"\b(?:_root_\.)?[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
RE_EXPLICIT_AT = re.compile(r"(?:^|[\s(\[{])@[A-Za-z_]")
RE_NS_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.']+)")
RE_NS_END = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.']+))?")
RE_OPEN = re.compile(r"^\s*open\s+(.+)$")
RE_VAR = re.compile(r"^\s*variable\s+(.+)$")
RE_UNIV = re.compile(r"^\s*universe\s+(.+)$")
# Simple local binder extractor (fun / ∀ / intro / let / have / obtain / (x : T) / {x : T})
RE_BINDER_VAR = re.compile(
    r"(?:[\(\{\[]\s*([a-zA-Z_][a-zA-Z0-9_']*(?:\s+[a-zA-Z_][a-zA-Z0-9_']*)*)\s*:|\b(?:fun|intro|intros|let|letI|set|have)\s+([a-zA-Z_][a-zA-Z0-9_']*))"
)

LEAN_KEYWORDS = {
    "theorem", "lemma", "def", "abbrev", "axiom", "opaque", "structure", "class",
    "inductive", "instance", "where", "by", "fun", "forall", "let", "letI", "have",
    "show", "from", "match", "with", "if", "then", "else", "do", "return", "in",
    "at", "using", "Type", "Prop", "Sort", "Nat", "Int", "Bool", "String", "Unit",
    "True", "False", "And", "Or", "Not", "Eq", "Iff", "Exists", "Subtype", "Sigma",
    "Prod", "Sum", "Option", "List", "Array", "Fin", "Char", "PUnit", "Empty",
    "private", "protected", "noncomputable", "partial", "unsafe", "local", "scoped",
    "section", "namespace", "end", "open", "import", "variable", "universe", "set_option",
    "intro", "intros", "rintro", "rcases", "obtain", "exact", "apply", "refine",
    "rw", "erw", "rwa", "simp", "simp_all", "dsimp", "simpa", "ring", "omega",
    "linarith", "nlinarith", "positivity", "field_simp", "norm_num", "norm_cast",
    "push_cast", "push_neg", "cases", "induction", "by_cases", "by_contra",
    "ext", "funext", "congr", "convert", "calc", "change", "unfold", "subst",
    "clear", "specialize", "generalize", "rfl", "trivial", "contradiction",
    "exfalso", "constructor", "left", "right", "use", "classical", "infer_instance",
    "nat_lit", "ite", "dite", "id", "Function", "Set", "Subgroup", "Submodule",
    "Matrix", "Complex", "Real", "ENNReal", "NNReal", "Rat", "Finset", "Fintype",
    "Polynomial", "RingHom", "MonoidHom", "LinearMap", "ContinuousLinearMap",
    "CommRing", "Field", "Semiring", "Ring", "Group", "Monoid", "Module", "Algebra",
    "AddCommGroup", "AddCommMonoid", "TopologicalSpace", "MeasurableSpace",
    "NormedAddCommGroup", "InnerProductSpace", "Representation", "NumberField",
    "Subalgebra", "FractionRing", "IsFractionRing", "IsLocalRing", "Valuation",
    "ValuativeRel", "Units", "Equiv", "Order", "Filter", "Measure",
    "carrier", "one_mem'", "mul_mem'", "inv_mem'", "toFun", "map_one'", "map_mul'",
    "inst", "inst_1", "inst_2", "inst_3", "inst_4", "inst_5", "u_1", "u_2",
}

PROJECT_ROOT_PREFIXES = (
    "UpperTheory.", "GlobalTheory.", "Development.", "Formalism.",
    "GroundTheory.", "ReciprocityTheory.", "CompanionTheory.",
    "PositivityTheory.", "Lemmata.",
)


def strip_comments(text: str) -> str:
    out = []
    i, n = 0, len(text)
    block = 0
    while i < n:
        if text[i : i + 2] == "/-":
            block += 1
            i += 2
        elif text[i : i + 2] == "-/" and block > 0:
            block -= 1
            i += 2
        elif block == 0 and text[i : i + 2] == "--":
            nl = text.find("\n", i)
            if nl == -1:
                break
            out.append("\n")
            i = nl + 1
        else:
            if block == 0:
                out.append(text[i])
            i += 1
    return "".join(out)


def clean_decl_name(name: str) -> str:
    """Normalize universe-polymorphic names indexed with trailing '.' (e.g. `Foo.bar.` -> `Foo.bar`)."""
    n = name.strip()
    if n.startswith("_root_."):
        n = n[7:]
    return n.rstrip(".")


def extract_bound_vars(code: str) -> set[str]:
    bound: set[str] = set()
    for m in RE_BINDER_VAR.finditer(code):
        if m.group(1):
            for tok in m.group(1).split():
                bound.add(tok)
        elif m.group(2):
            bound.add(m.group(2))
    return bound


def split_sig_body_stats(decl_lines: list[str]) -> tuple[int, int, int, int]:
    found = False
    sig_end = len(decl_lines)
    at_sig = 0
    at_body = 0
    for idx, line in enumerate(decl_lines, start=1):
        code = line.split("--", 1)[0]
        if not found:
            if ":=" in code:
                found = True
                sig_end = idx
                before, after = code.split(":=", 1)
                if RE_EXPLICIT_AT.search(before):
                    at_sig += 1
                if RE_EXPLICIT_AT.search(after):
                    at_body += 1
            else:
                if RE_EXPLICIT_AT.search(code):
                    at_sig += 1
        else:
            if RE_EXPLICIT_AT.search(code):
                at_body += 1
    sig_lns = sig_end if found else len(decl_lines)
    body_lns = max(0, len(decl_lines) - sig_lns)
    return sig_lns, body_lns, at_sig, at_body


def extract_context_directives(lines: list[str], up_to_line: int) -> tuple[list[str], list[str], list[str], list[str]]:
    ns_stack: list[str] = []
    opens: list[str] = []
    univs: list[str] = []
    vars_list: list[str] = []
    for ln in lines[: max(0, up_to_line - 1)]:
        s = ln.split("--", 1)[0].strip()
        if not s:
            continue
        if m := RE_NS_OPEN.match(s):
            ns_stack.append(m.group(1))
        elif m := RE_NS_END.match(s):
            if ns_stack:
                ns_stack.pop()
        elif m := RE_OPEN.match(s):
            if s not in opens:
                opens.append(s)
        elif m := RE_UNIV.match(s):
            if s not in univs:
                univs.append(s)
        elif m := RE_VAR.match(s):
            if s not in vars_list:
                vars_list.append(s)
    return ns_stack, opens, univs, vars_list


def generate_stub(
    module: str,
    decl_name: str,
    out_path: Path,
    mode: str = "mathlib",
    include_local_deps: bool = True,
    db_path: Path = DEFAULT_INDEX_DB,
    src_root: Path = DEFAULT_SRC_ROOT,
) -> dict:
    import duckdb

    con = duckdb.connect(str(db_path), read_only=True)
    mod_row = con.execute(
        "SELECT rel_path, lines, has_mathlib_import, import_count, decl_count FROM modules WHERE module = ?",
        [module],
    ).fetchone()
    if not mod_row:
        raise ValueError(f"Module not found in DuckDB: {module}")
    rel_path, mod_lines, has_mathlib, imp_cnt, decl_cnt = mod_row

    mod_decls = con.execute(
        "SELECT kind, name, start_line, end_line, span_lines, signature FROM decls WHERE module = ? ORDER BY start_line",
        [module],
    ).fetchall()

    target = None
    want = clean_decl_name(decl_name)
    for row in mod_decls:
        cn = clean_decl_name(row[1])
        if cn == want or cn.endswith("." + want):
            target = row
            if cn == want:
                break
    if target is None:
        avail = [clean_decl_name(r[1]) for r in mod_decls[:15]]
        raise ValueError(f"Declaration '{decl_name}' not found in {module}. Sample decls: {avail}")

    t_kind, t_name_raw, t_start, t_end, t_span, t_sig = target
    t_name = clean_decl_name(t_name_raw)
    file_path = src_root / rel_path
    all_lines = file_path.read_text(encoding="utf-8", errors="replace").splitlines()

    decl_by_idx = {}
    name_to_idxs: dict[str, list[int]] = {}
    target_idx = -1
    for idx, r in enumerate(mod_decls):
        k, nm_raw, sl, el, sp, sg = r
        nm = clean_decl_name(nm_raw)
        txt = "\n".join(all_lines[sl - 1 : el])
        decl_by_idx[idx] = (k, nm, sl, el, sp, sg, txt)
        name_to_idxs.setdefault(nm, []).append(idx)
        tail = nm.rsplit(".", 1)[-1]
        if tail and tail != "<anonymous>":
            name_to_idxs.setdefault(tail, []).append(idx)
        if nm == t_name and sl == t_start:
            target_idx = idx

    # Transitively resolve local dependencies defined earlier in the same module
    selected_idxs: set[int] = {target_idx}
    if include_local_deps:
        queue = [target_idx]
        while queue:
            cur = queue.pop()
            cur_txt = strip_comments(decl_by_idx[cur][6])
            refs = set(RE_IDENT.findall(cur_txt))
            for r in refs:
                rc = clean_decl_name(r)
                candidates = name_to_idxs.get(rc, [])
                if not candidates and "." in rc:
                    candidates = name_to_idxs.get(rc.rsplit(".", 1)[-1], [])
                for cidx in candidates:
                    if cidx < cur and cidx not in selected_idxs:
                        selected_idxs.add(cidx)
                        queue.append(cidx)

    ordered_selected = sorted(selected_idxs)
    local_dep_idxs = [i for i in ordered_selected if i != target_idx]

    combined_code = "\n".join(strip_comments(decl_by_idx[i][6]) for i in ordered_selected)
    all_refs = sorted(set(RE_IDENT.findall(combined_code)))
    bound_vars = extract_bound_vars(combined_code)
    local_names = {decl_by_idx[i][1] for i in ordered_selected} | {
        decl_by_idx[i][1].rsplit(".", 1)[-1] for i in ordered_selected
    }

    # Query direct + 2-hop local imports in DuckDB
    direct_imports = [
        r[0] for r in con.execute("SELECT dst_module FROM imports WHERE src_module = ?", [module]).fetchall()
    ]
    local_imports = [m for m in direct_imports if not (m == "Mathlib" or m.startswith("Mathlib."))]
    mathlib_imports = [m for m in direct_imports if (m == "Mathlib" or m.startswith("Mathlib."))]

    ext_decls_by_name: dict[str, tuple[str, str, str, str]] = {}
    ext_decls_by_tail: dict[str, list[tuple[str, str, str, str]]] = {}
    if local_imports:
        hop2 = [
            r[0]
            for r in con.execute(
                "SELECT DISTINCT dst_module FROM imports WHERE src_module IN (SELECT UNNEST(?))",
                [local_imports],
            ).fetchall()
        ]
        hop3 = [
            r[0]
            for r in con.execute(
                "SELECT DISTINCT dst_module FROM imports WHERE src_module IN (SELECT UNNEST(?))",
                [hop2[:300]] if hop2 else [[]],
            ).fetchall()
        ] if hop2 else []
        search_mods = sorted(
            {m for m in (set(local_imports) | set(hop2) | set(hop3)) if not m.startswith("Mathlib")}
        )
        if search_mods:
            rows = con.execute(
                "SELECT module, kind, name, signature FROM decls WHERE module IN (SELECT UNNEST(?))",
                [search_mods],
            ).fetchall()
            for m, k, nm_raw, sg in rows:
                nm = clean_decl_name(nm_raw)
                ext_decls_by_name[nm] = (m, k, nm, sg)
                ext_decls_by_tail.setdefault(nm.rsplit(".", 1)[-1], []).append((m, k, nm, sg))

    matched_ext: dict[str, tuple[str, str, str, str]] = {}
    unresolved_project_refs: list[str] = []
    mathlib_or_stdlib_refs: list[str] = []

    for ref in all_refs:
        rc = clean_decl_name(ref)
        if not rc or rc in local_names or rc in LEAN_KEYWORDS:
            continue
        if "." not in rc and (len(rc) < 3 or rc in bound_vars):
            continue
        if rc in ext_decls_by_name:
            matched_ext[rc] = ext_decls_by_name[rc]
            continue
        tail = rc.rsplit(".", 1)[-1]
        if "." in rc and rc.startswith(PROJECT_ROOT_PREFIXES):
            # 1) Exact match in entire DB
            hit = con.execute(
                "SELECT module, kind, name, signature FROM decls WHERE name = ? OR name = ? OR name = ? LIMIT 1",
                [rc, "_root_." + rc, rc + "."],
            ).fetchone()
            if hit:
                matched_ext[rc] = (hit[0], hit[1], rc, hit[3])
            elif tail in ext_decls_by_tail:
                # Match namespace-scoped declaration inside imported modules (e.g. `GLw` inside `namespace UpperTheory.V.Hi`)
                cands = ext_decls_by_tail[tail]
                # Prefer direct import if present
                direct_set = set(local_imports)
                cands_sorted = sorted(cands, key=lambda x: (0 if x[0] in direct_set else 1, x[0]))
                best = cands_sorted[0]
                matched_ext[rc] = (best[0], best[1], rc, best[3])
            else:
                unresolved_project_refs.append(rc)
        elif "." not in rc:
            # Only resolve unqualified identifiers that are NOT bound variables and >= 3 chars
            if len(rc) >= 3 and rc not in bound_vars and rc in ext_decls_by_tail:
                cands = ext_decls_by_tail[rc]
                direct_set = set(local_imports)
                direct_cands = [c for c in cands if c[0] in direct_set]
                if len(direct_cands) == 1:
                    matched_ext[rc] = direct_cands[0]
                elif len(cands) == 1:
                    matched_ext[rc] = cands[0]
        else:
            mathlib_or_stdlib_refs.append(rc)

    target_lines_list = all_lines[t_start - 1 : t_end]
    sig_lns, body_lns, at_sig, at_body = split_sig_body_stats(target_lines_list)
    ns_stack, opens, univs, vars_list = extract_context_directives(all_lines, t_start)

    out_lines: list[str] = []
    out_lines.append("/-")
    out_lines.append("  ==========================================================================")
    out_lines.append("  Standalone Proof-Golfing Sandbox Stub (generated by make_stub.py)")
    out_lines.append("  ==========================================================================")
    out_lines.append(f"  Source Module        : {module}")
    out_lines.append(f"  Source File          : {rel_path}")
    out_lines.append(f"  Target Declaration   : {t_kind} {t_name}")
    out_lines.append(f"  Original Line Range  : L{t_start}..L{t_end} ({t_span} lines)")
    out_lines.append(f"    - Signature lines  : {sig_lns} (explicit-@ lines: {at_sig})")
    out_lines.append(f"    - Proof/Body lines : {body_lns} (explicit-@ lines: {at_body})")
    out_lines.append(f"  Local Deps Included  : {len(local_dep_idxs)} declarations")
    out_lines.append(f"  External Proj Stubs  : {len(matched_ext)} matched + {len(unresolved_project_refs)} unresolved")
    out_lines.append(f"  Mathlib/Std Refs     : {len(mathlib_or_stdlib_refs)} distinct dotted identifiers")
    out_lines.append(f"  Stub Mode            : {mode}")
    out_lines.append("  Repo Toolchain       : leanprover/lean4:v4.33.1 (requires Mathlib oleans for full mode)")
    out_lines.append("  Verify Command (4.33): elan run leanprover/lean4:v4.33.1 lake env lean <this_file>")
    out_lines.append("-/")
    out_lines.append("")

    if mode == "mathlib":
        if mathlib_imports:
            for mi in mathlib_imports:
                out_lines.append(f"import {mi}")
        elif has_mathlib:
            out_lines.append("import Mathlib")
        else:
            out_lines.append("-- Note: original module had no direct `import Mathlib`; transitive Mathlib assumed:")
            out_lines.append("import Mathlib")
        out_lines.append("")
    else:
        out_lines.append("-- Pure Lean 4 core sandbox mode (no Mathlib import; external symbols stubbed below)")
        out_lines.append("")

    if univs:
        out_lines.extend(univs)
    if opens and mode == "mathlib":
        out_lines.extend(opens)
    if univs or (opens and mode == "mathlib"):
        out_lines.append("")

    if matched_ext or unresolved_project_refs:
        out_lines.append("/-! ### External Project Dependency Stubs (from imported local modules) -/")
        out_lines.append("")
        for ref_name in sorted(matched_ext.keys()):
            emod, ekind, efname, esig = matched_ext[ref_name]
            out_lines.append(f"-- Origin: {emod} ({ekind} {efname})")
            out_lines.append(f"-- Original signature: {esig[:220]}")
            stub_kw = "axiom" if ekind in ("theorem", "lemma", "axiom") else "opaque"
            clean_nm = clean_decl_name(efname)
            if stub_kw == "axiom":
                out_lines.append(f"axiom {clean_nm} : True -- replace with full type under Mathlib oleans")
            else:
                out_lines.append(f"opaque {clean_nm} : Type -- replace with full type under Mathlib oleans")
            out_lines.append("")

        for uref in sorted(unresolved_project_refs):
            out_lines.append(f"-- Unresolved project reference (transitive >3-hop or generated): {uref}")
            out_lines.append(f"opaque {uref} : Type")
            out_lines.append("")

    if local_dep_idxs:
        out_lines.append(f"/-! ### Local Module Dependencies ({len(local_dep_idxs)} declarations from {module}) -/")
        out_lines.append("")
        for idx in local_dep_idxs:
            k, nm, sl, el, sp, sg, txt = decl_by_idx[idx]
            out_lines.append(f"-- [local dep] {k} {nm} (L{sl}..L{el}, {sp} lines)")
            out_lines.append(txt)
            out_lines.append("")

    out_lines.append("/-! ### Target Declaration Under Golfing -/")
    out_lines.append("")
    if ns_stack:
        for ns in ns_stack:
            out_lines.append(f"namespace {ns}")
    if vars_list:
        out_lines.extend(vars_list)
    out_lines.append(decl_by_idx[target_idx][6])
    if ns_stack:
        for ns in reversed(ns_stack):
            out_lines.append(f"end {ns}")
    out_lines.append("")

    full_text = "\n".join(out_lines)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(full_text, encoding="utf-8")
    con.close()

    return {
        "module": module,
        "decl": t_name,
        "kind": t_kind,
        "start_line": t_start,
        "end_line": t_end,
        "orig_span_lines": t_span,
        "sig_lines": sig_lns,
        "body_lines": body_lns,
        "at_sig_lines": at_sig,
        "at_body_lines": at_body,
        "local_deps_count": len(local_dep_idxs),
        "external_proj_stubs_matched": len(matched_ext),
        "external_proj_stubs_unresolved": len(unresolved_project_refs),
        "mathlib_refs_count": len(mathlib_or_stdlib_refs),
        "out_file": str(out_path),
        "out_lines": len(full_text.splitlines()),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate standalone Lean 4 stub for proof-golfing sandbox.")
    add_path_arguments(parser)
    parser.add_argument("--module", required=True, help="Fully qualified Lean module name")
    parser.add_argument("--decl", required=True, help="Declaration name (full or suffix)")
    parser.add_argument("--out", type=Path, help="Output .lean file (default: OUT_DIR/stub.lean)")
    parser.add_argument("--mode", choices=["mathlib", "pure-core"], default="mathlib", help="Stub header mode")
    parser.add_argument("--no-local-deps", action="store_true", help="Do not include local helper declarations")
    args = parser.parse_args()
    src_root, db_path, out_dir = resolve_paths(args)

    meta = generate_stub(
        module=args.module,
        decl_name=args.decl,
        out_path=args.out or out_dir / "stub.lean",
        db_path=db_path,
        src_root=src_root,
        mode=args.mode,
        include_local_deps=not args.no_local_deps,
    )
    print("Generated stub successfully:")
    for k, v in meta.items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    main()
