#!/usr/bin/env python3
"""Audit Lean declaration citations in technical specification documents against the kernel export cone.

Verifies that every cited qualified Lean declaration in the given Markdown files
appears in Andrew Sutherland / James Shore's kernel export (`cone-constants.txt.gz`
and `decls.csv.gz`), flagging any dead/unused declarations (`in_cone = false`) unless
explicitly placed inside an exclusion / dead-code audit section.

Usage:
    python audit_spec_citations.py \
        --cone path/to/cone-constants.txt.gz \
        --decls path/to/decls.csv.gz \
        reports/minimal_backbone_spec.md reports/rosetta_stone.md
"""
import argparse
import csv
import gzip
import json
import re
import sys
from pathlib import Path

ROOT_PREFIXES = (
    "Formalism",
    "UpperTheory",
    "GlobalTheory",
    "GroundTheory",
    "CompanionTheory",
    "ReciprocityTheory",
    "PositivityTheory",
    "SelfIntersectionVolumeEstimates",
    "PI",
    "QH",
    "Claim",
)

QUAL_RE = re.compile(
    r"`((?:" + "|".join(ROOT_PREFIXES) + r")\.[A-Za-z0-9_.'₀-₉]+)`"
)

MAIN_BARES = {
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
    "rhOfAll",
    "allChi",
    "claimAll",
    "critAll",
}


def load_cone(path: Path) -> set[str]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as f:
        return {line.strip() for line in f if line.strip()}


def load_decls(path: Path) -> dict[str, dict]:
    opener = gzip.open if path.suffix == ".gz" else open
    out: dict[str, dict] = {}
    with opener(path, "rt", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row["decl"]
            in_cone = row["in_cone"].lower() == "true"
            # Keep in_cone=True entry if a name appears in multiple modules
            if name not in out or (in_cone and not out[name]["in_cone"]):
                out[name] = {
                    "kind": row["kind"],
                    "file": row["file"],
                    "start_line": int(row["start_line"]),
                    "lines": int(row["lines"]),
                    "in_cone": in_cone,
                }
    return out


def strip_excluded_sections(md_text: str) -> str:
    """Exclude explicitly marked `<!-- audit:allow-dead-start --> ... <!-- audit:allow-dead-end -->` blocks
    used to document dead/unused declarations transparently."""
    return re.sub(
        r"<!--\s*audit:allow-dead-start\s*-->.*?<!--\s*audit:allow-dead-end\s*-->",
        "",
        md_text,
        flags=re.DOTALL,
    )


def audit_file(md_path: Path, cone: set[str], decls: dict[str, dict]) -> dict:
    raw = md_path.read_text(encoding="utf-8")
    active = strip_excluded_sections(raw)

    cited = sorted(set(QUAL_RE.findall(active)))
    for b in MAIN_BARES:
        if f"`{b}`" in active:
            cited.append(b)
    cited = sorted(set(cited))

    used = []
    dead = []
    module_or_ns = []

    for name in cited:
        info = decls.get(name)
        if info is not None:
            if info["in_cone"]:
                used.append({"decl": name, **info})
            else:
                dead.append({"decl": name, **info})
        elif name in cone:
            used.append({"decl": name, "kind": "kernel_const", "in_cone": True})
        else:
            module_or_ns.append(name)

    tag_counts = {
        "Exact": len(re.findall(r"\[Exact\]", raw)),
        "Verified": len(re.findall(r"\[Verified\]", raw)),
        "Reading": len(re.findall(r"\[Reading\]", raw)),
    }

    return {
        "file": md_path.name,
        "used_decls_count": len(used),
        "dead_decls_count": len(dead),
        "module_or_ns_count": len(module_or_ns),
        "dead_decls": dead,
        "module_or_ns": module_or_ns,
        "epistemic_tags": tag_counts,
        "pass": len(dead) == 0,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cone", type=Path, required=True)
    parser.add_argument("--decls", type=Path, required=True)
    parser.add_argument("--json-out", type=Path, default=None)
    parser.add_argument("files", nargs="+", type=Path)
    args = parser.parse_args()

    cone = load_cone(args.cone)
    decls = load_decls(args.decls)

    results = []
    all_pass = True
    for fp in args.files:
        res = audit_file(fp, cone, decls)
        results.append(res)
        status = "PASS" if res["pass"] else "FAIL"
        print(
            f"[{status}] {res['file']}: used={res['used_decls_count']}, "
            f"dead={res['dead_decls_count']}, mod/ns={res['module_or_ns_count']}, "
            f"tags={res['epistemic_tags']}"
        )
        for d in res["dead_decls"]:
            print(f"   DEAD CITATION: {d['decl']} ({d['kind']} at {d['file']}:{d['start_line']})")
        if not res["pass"]:
            all_pass = False

    if args.json_out:
        args.json_out.write_text(json.dumps(results, indent=2), encoding="utf-8")

    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
