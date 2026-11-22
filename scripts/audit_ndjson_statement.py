#!/usr/bin/env python3
"""Lean-free auditor for raw kernel statements and axioms in lean4export 3.1.0 NDJSON files.

Parses `challenge.ndjson` (or `.ndjson.zst`) using Python's standard library only—no Lean
toolchain required—to verify the uncompressed SHA-256, audit every declaration's axioms and
safety flags (including `opaque`, `inductive` ctors/recs, and auxiliary `_proof_k` terms
inside statement types), and pretty-print the raw kernel statement ASTs of the five RH/GRH
headline theorems.

Usage:
    python scripts/audit_ndjson_statement.py path/to/challenge.ndjson.zst
    python scripts/audit_ndjson_statement.py --mode solution path/to/solution.ndjson.zst
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from contextlib import contextmanager
from pathlib import Path
from typing import Any

STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
HEADLINE_THEOREMS = [
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
]


@contextmanager
def open_ndjson(path: Path, window_log_max: int):
    if path.suffix != ".zst":
        with path.open("rb") as f:
            yield f
        return
    try:
        from compression import zstd  # Python 3.14+ stdlib
        opts = {zstd.DecompressionParameter.window_log_max: window_log_max}
        with zstd.open(path, "rb", options=opts) as f:
            yield f
    except ImportError:
        proc = subprocess.Popen(
            ["zstd", "-dc", f"--long={window_log_max}", str(path)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        assert proc.stdout is not None and proc.stderr is not None
        failed = False
        try:
            yield proc.stdout
        except BaseException:
            failed = True
            proc.terminate()
            raise
        finally:
            proc.stdout.close()
            err = proc.stderr.read().decode("utf-8", "replace")
            proc.stderr.close()
            rc = proc.wait()
            if not failed and rc != 0:
                raise RuntimeError(f"zstd decompression failed (exit {rc}): {err.strip()}")


def parse_export(path: Path, window_log_max: int) -> dict[str, Any]:
    names: dict[int, str] = {0: ""}
    exprs: dict[int, tuple] = {}
    decls: dict[str, dict[str, Any]] = {}
    meta: dict[str, Any] = {}
    axioms: list[str] = []
    unsafe: list[str] = []
    kind_counts = {"axiom": 0, "def": 0, "opaque": 0, "thm": 0, "inductive": 0, "quot": 0}
    sha = hashlib.sha256()
    nbytes = 0
    nlines = 0

    with open_ndjson(path, window_log_max) as f:
        for raw in f:
            nbytes += len(raw)
            sha.update(raw)
            nlines += 1
            obj = json.loads(raw)
            if "in" in obj:
                idx = obj["in"]
                if "str" in obj:
                    p = names[obj["str"]["pre"]]
                    s = obj["str"]["str"]
                    names[idx] = f"{p}.{s}" if p else s
                else:
                    p = names[obj["num"]["pre"]]
                    names[idx] = f"{p}.{obj['num']['i']}" if p else str(obj["num"]["i"])
            elif "ie" in obj:
                idx = obj["ie"]
                if "const" in obj:
                    exprs[idx] = ("const", names[obj["const"]["name"]])
                elif "app" in obj:
                    a = obj["app"]
                    exprs[idx] = ("app", a["fn"], a["arg"])
                elif "forallE" in obj:
                    e = obj["forallE"]
                    exprs[idx] = ("forallE", names[e["name"]], e["type"], e["body"], e["binderInfo"])
                elif "lam" in obj:
                    e = obj["lam"]
                    exprs[idx] = ("lam", names[e["name"]], e["type"], e["body"], e["binderInfo"])
                elif "letE" in obj:
                    e = obj["letE"]
                    exprs[idx] = ("letE", names[e["name"]], e["type"], e["value"], e["body"])
                elif "proj" in obj:
                    p = obj["proj"]
                    exprs[idx] = ("proj", names[p["typeName"]], p["idx"], p["struct"])
                elif "bvar" in obj:
                    exprs[idx] = ("bvar", obj["bvar"])
                elif "sort" in obj:
                    exprs[idx] = ("sort", obj["sort"])
                elif "natVal" in obj:
                    exprs[idx] = ("natVal", obj["natVal"])
                elif "strVal" in obj:
                    exprs[idx] = ("strVal", obj["strVal"])
            elif "thm" in obj:
                t = obj["thm"]
                nm = names[t["name"]]
                kind_counts["thm"] += 1
                decls[nm] = {"kind": "thm", "type": t["type"], "value": t["value"]}
            elif "def" in obj:
                d = obj["def"]
                nm = names[d["name"]]
                kind_counts["def"] += 1
                if d.get("safety") != "safe":
                    unsafe.append(f"def:{nm}({d.get('safety')})")
                decls[nm] = {"kind": "def", "type": d["type"], "value": d["value"]}
            elif "opaque" in obj:
                o = obj["opaque"]
                nm = names[o["name"]]
                kind_counts["opaque"] += 1
                if o.get("isUnsafe"):
                    unsafe.append(f"opaque:{nm}")
                decls[nm] = {"kind": "opaque", "type": o["type"], "value": o["value"]}
            elif "axiom" in obj:
                a = obj["axiom"]
                nm = names[a["name"]]
                kind_counts["axiom"] += 1
                axioms.append(nm)
                if a.get("isUnsafe"):
                    unsafe.append(f"axiom:{nm}")
                decls[nm] = {"kind": "axiom", "type": a["type"]}
            elif "inductive" in obj:
                ind = obj["inductive"]
                kind_counts["inductive"] += 1
                ctors = ind.get("ctors", [])
                for t in ind.get("types", []):
                    nm = names[t["name"]]
                    if t.get("isUnsafe"):
                        unsafe.append(f"ind:{nm}")
                    ctor_types = [c["type"] for c in ctors if names[c["induct"]] == nm]
                    deps = [names[x] for x in t.get("all", []) if names[x] != nm]
                    decls[nm] = {"kind": "inductive", "type": t["type"], "extra": ctor_types, "deps": deps}
                for c in ctors:
                    nm = names[c["name"]]
                    if c.get("isUnsafe"):
                        unsafe.append(f"ctor:{nm}")
                    decls[nm] = {"kind": "ctor", "type": c["type"], "deps": [names[c["induct"]]]}
                for r in ind.get("recs", []):
                    nm = names[r["name"]]
                    if r.get("isUnsafe"):
                        unsafe.append(f"rec:{nm}")
                    rule_rhs = [rule["rhs"] for rule in r.get("rules", []) if "rhs" in rule]
                    deps = [names[x] for x in r.get("all", [])]
                    decls[nm] = {"kind": "rec", "type": r["type"], "extra": rule_rhs, "deps": deps}
            elif "quot" in obj:
                q = obj["quot"]
                kind_counts["quot"] += 1
                decls[names[q["name"]]] = {"kind": "quot", "type": q["type"]}
            elif "meta" in obj:
                meta = obj["meta"]

    return {
        "meta": meta, "nbytes": nbytes, "nlines": nlines, "sha256": sha.hexdigest(),
        "kind_counts": kind_counts, "axioms": axioms, "unsafe": unsafe,
        "exprs": exprs, "decls": decls,
    }


def expr_consts(eid: int, exprs: dict[int, tuple]) -> set[str]:
    out: set[str] = set()
    stack = [eid]
    seen: set[int] = set()
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        node = exprs[cur]
        tag = node[0]
        if tag == "const":
            out.add(node[1])
        elif tag == "app":
            stack.extend((node[1], node[2]))
        elif tag in ("forallE", "lam"):
            stack.extend((node[2], node[3]))
        elif tag == "letE":
            stack.extend((node[2], node[3], node[4]))
        elif tag == "proj":
            out.add(node[1])
            stack.append(node[3])
    return out


def closure(
    roots: set[str], decls: dict[str, dict[str, Any]], exprs: dict[int, tuple], follow_thm_value: bool
) -> dict[str, Any]:
    visited: set[str] = set()
    missing: set[str] = set()
    stack = list(roots)
    kinds: dict[str, int] = {}
    axioms_used: set[str] = set()
    while stack:
        nm = stack.pop()
        if nm in visited:
            continue
        d = decls.get(nm)
        if d is None:
            missing.add(nm)
            continue
        visited.add(nm)
        k = d["kind"]
        kinds[k] = kinds.get(k, 0) + 1
        if k == "axiom":
            axioms_used.add(nm)
        eids = [d["type"]]
        if k in ("def", "opaque") or (k == "thm" and follow_thm_value):
            eids.append(d["value"])
        if "extra" in d:
            eids.extend(d["extra"])
        for dep in d.get("deps", ()):
            if dep not in visited:
                stack.append(dep)
        for eid in eids:
            stack.extend(expr_consts(eid, exprs) - visited)
    return {"total": len(visited), "kinds": kinds, "axioms": sorted(axioms_used), "missing": sorted(missing)}


def has_bvar(eid: int, target: int, exprs: dict[int, tuple]) -> bool:
    stack = [(eid, target)]
    seen: set[tuple[int, int]] = set()
    while stack:
        cur, d = stack.pop()
        if (cur, d) in seen:
            continue
        seen.add((cur, d))
        node = exprs[cur]
        tag = node[0]
        if tag == "bvar":
            if node[1] == d:
                return True
        elif tag == "app":
            stack.extend(((node[1], d), (node[2], d)))
        elif tag in ("forallE", "lam"):
            stack.extend(((node[2], d), (node[3], d + 1)))
        elif tag == "letE":
            stack.extend(((node[2], d), (node[3], d), (node[4], d + 1)))
        elif tag == "proj":
            stack.append((node[3], d))
    return False


def clean_binder(nm: str) -> str:
    return nm.split("._@.", 1)[0] if "._@." in nm else (nm or "_")


def pp_expr(eid: int, exprs: dict[int, tuple], env: tuple[str, ...] = (), prec: int = 0) -> str:
    node = exprs[eid]
    tag = node[0]
    if tag == "bvar":
        idx = node[1]
        return env[idx] if idx < len(env) else f"#{idx}"
    if tag == "const":
        return node[1]
    if tag == "sort":
        return "Prop" if node[1] == 0 else f"Sort u{node[1]}"
    if tag == "natVal":
        return str(node[1])
    if tag == "strVal":
        return json.dumps(node[1])
    if tag == "proj":
        return f"({pp_expr(node[3], exprs, env, 2)}.{node[2]})"
    if tag == "app":
        parts = []
        cur = eid
        while exprs[cur][0] == "app":
            parts.append(exprs[cur][2])
            cur = exprs[cur][1]
        head = pp_expr(cur, exprs, env, 2)
        args = " ".join(pp_expr(a, exprs, env, 2) for a in reversed(parts))
        s = f"{head} {args}"
        return f"({s})" if prec >= 2 else s
    if tag == "forallE":
        _, raw_nm, ty, body, bi = node
        nm = clean_binder(raw_nm)
        is_arrow = bi == "default" and not has_bvar(body, 0, exprs)
        ty_s = pp_expr(ty, exprs, env, 1 if is_arrow else 0)
        b_s = pp_expr(body, exprs, (nm,) + env, 0)
        br = {"implicit": ("{", "}"), "strictImplicit": ("⦃", "⦄"), "instImplicit": ("[", "]")}.get(bi, ("(", ")"))
        s = f"{ty_s} → {b_s}" if is_arrow else f"∀ {br[0]}{nm} : {ty_s}{br[1]}, {b_s}"
        return f"({s})" if prec >= 1 else s
    if tag == "lam":
        _, raw_nm, ty, body, _ = node
        nm = clean_binder(raw_nm)
        s = f"fun ({nm} : {pp_expr(ty, exprs, env, 0)}) => {pp_expr(body, exprs, (nm,) + env, 0)}"
        return f"({s})" if prec >= 1 else s
    if tag == "letE":
        _, raw_nm, ty, val, body = node
        nm = clean_binder(raw_nm)
        s = f"let {nm} : {pp_expr(ty, exprs, env, 0)} := {pp_expr(val, exprs, env, 0)}; {pp_expr(body, exprs, (nm,) + env, 0)}"
        return f"({s})" if prec >= 1 else s
    return f"<{tag}>"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("ndjson", type=Path, help="Path to challenge.ndjson(.zst) or solution.ndjson(.zst)")
    ap.add_argument("--mode", choices=("challenge", "solution"), default="challenge")
    ap.add_argument("--targets", nargs="+", default=HEADLINE_THEOREMS)
    ap.add_argument("--window-log-max", type=int, default=27, help="zstd --long parameter (27 challenge, 30 solution)")
    ap.add_argument("--expected-sha256", default=None)
    ap.add_argument("--json-out", type=Path, default=None)
    args = ap.parse_args()

    data = parse_export(args.ndjson, args.window_log_max)
    exprs, decls = data["exprs"], data["decls"]
    n_records = sum(data["kind_counts"].values())
    print(f"File:    {args.ndjson.name} ({data['nbytes']:,} unpacked bytes, {data['nlines']:,} lines)")
    print(f"SHA-256: {data['sha256']}")
    print(f"Meta:    {data['meta']}")
    print(f"Decls:   {n_records:,} top-level records {data['kind_counts']} | named entries={len(decls):,} | unsafe={len(data['unsafe'])}")
    print(f"Axioms:  {sorted(data['axioms'])}")

    ok = not data["unsafe"]
    if args.expected_sha256 and data["sha256"] != args.expected_sha256.lower():
        print(f"[FAIL] SHA-256 mismatch: expected {args.expected_sha256}")
        ok = False

    report: dict[str, Any] = {
        "sha256": data["sha256"], "nbytes": data["nbytes"], "records": n_records,
        "kind_counts": data["kind_counts"], "axioms": sorted(data["axioms"]),
        "unsafe": data["unsafe"], "targets": {},
    }
    allowed_proof_axioms = STD_AXIOMS | ({"sorryAx"} if args.mode == "challenge" else set())

    for name in args.targets:
        d = decls.get(name)
        if not d:
            print(f"\n[FAIL] Missing target declaration: {name}")
            ok = False
            continue
        ty_id = d["type"]
        raw_ty = pp_expr(ty_id, exprs)
        unfolded_name, unfolded_id = None, ty_id
        if exprs[ty_id][0] == "const" and exprs[ty_id][1] in decls and decls[exprs[ty_id][1]]["kind"] == "def":
            unfolded_name = exprs[ty_id][1]
            unfolded_id = decls[unfolded_name]["value"]
        direct = sorted(expr_consts(unfolded_id, exprs))
        type_roots = expr_consts(ty_id, exprs)
        stmt_def_cl = closure(type_roots, decls, exprs, follow_thm_value=False)
        stmt_full_cl = closure(type_roots, decls, exprs, follow_thm_value=True)
        proof_cl = closure({name}, decls, exprs, follow_thm_value=True)
        bad_stmt = set(stmt_full_cl["axioms"]) - STD_AXIOMS
        bad_proof = set(proof_cl["axioms"]) - allowed_proof_axioms
        missing_any = sorted(set(stmt_full_cl["missing"]) | set(proof_cl["missing"]))
        if bad_stmt or bad_proof or missing_any:
            ok = False
        print(f"\n=== {name} ({d['kind']}) ===")
        print(f"  Raw kernel type: {raw_ty}")
        if unfolded_name:
            print(f"  Unfolded {unfolded_name}:")
            print(f"    {pp_expr(unfolded_id, exprs)}")
        print(f"  Direct constants ({len(direct)}): {', '.join(direct)}")
        print(f"  Statement def-closure:  {stmt_def_cl['total']:,} decls {stmt_def_cl['kinds']} | axioms={stmt_def_cl['axioms']}")
        print(f"  Statement full-closure: {stmt_full_cl['total']:,} decls | axioms={stmt_full_cl['axioms']} | missing={len(stmt_full_cl['missing'])}")
        print(f"  Proof full-closure:     {proof_cl['total']:,} decls | axioms={proof_cl['axioms']} | missing={len(proof_cl['missing'])}")
        report["targets"][name] = {
            "kind": d["kind"], "raw_type": raw_ty, "unfolded_def": unfolded_name,
            "unfolded_type": pp_expr(unfolded_id, exprs) if unfolded_name else raw_ty,
            "direct_constants": direct, "stmt_def_closure": stmt_def_cl,
            "stmt_full_closure": stmt_full_cl, "proof_closure": proof_cl,
        }

    if args.json_out:
        args.json_out.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"\n[{'PASS' if ok else 'FAIL'}] Audited {len(args.targets)} target(s) in {args.mode} mode (unsafe={len(data['unsafe'])}).")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
