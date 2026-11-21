#!/usr/bin/env python3
"""
Task 2 Diff Profiler: `UnitaryGroupMassFormula` Triple-Directory Clone Analyzer.

Profiles all modules across:
  1. Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume
  2. Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume
  3. Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume

Computes:
  - Shared triplets (all 3), pairs (2 of 3), and directory-unique files
  - Raw line-by-line similarity AND normalized similarity (stripping/mapping
    directory-specific module/namespace prefixes)
  - Categorization: exact_norm (>=99.5%), near_identical (90-99.5%),
    high_similar (75-90%), moderate (40-75%), divergent (<40%)
  - Exact diff hunks for representative triplets to expose the mathematical /
    type-parameter axis differentiating the 3 directories
  - Exact conservative & aggressive line-reduction estimates from consolidation
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
from collections import Counter
from pathlib import Path

from index_lean import add_path_arguments, resolve_paths



PREFIX = "Formalism.PeriodIntegrals.UnitaryGroupMassFormula."
DIRS = [
    "StabilizerOrbitVolume",
    "StabilizerVolume",
    "WeilStabilizerVolume",
]


def normalize_for_dir(text: str, dir_name: str) -> str:
    """Normalize import paths and namespace tokens specific to one of the 3 directories."""
    out = text.replace(f"{PREFIX}{dir_name}", f"{PREFIX}<DIR>")
    # Also normalize internal short namespace tags if present
    # First inspect raw text; keep normalization strictly transparent!
    return out


def strip_imports_and_ns(lines: list[str]) -> list[str]:
    out = []
    for ln in lines:
        s = ln.strip()
        if not s:
            continue
        if s.startswith("import "):
            continue
        if s.startswith("namespace ") or s.startswith("end "):
            continue
        if s.startswith("open "):
            continue
        out.append(ln)
    return out


def detect_namespace_tags(lines: list[str]) -> list[str]:
    tags = []
    for ln in lines:
        m = re.match(r"^\s*namespace\s+(\S+)", ln)
        if m:
            tags.append(m.group(1))
    return tags


def normalize_body(lines: list[str], dir_name: str, ns_map: dict[str, str]) -> list[str]:
    out = []
    for ln in strip_imports_and_ns(lines):
        s = ln.replace(f"{PREFIX}{dir_name}", "<DIR>")
        for src_tok, dst_tok in ns_map.items():
            s = s.replace(src_tok, dst_tok)
        out.append(s)
    return out


def pair_sim(a: list[str], b: list[str]) -> float:
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    if a == b:
        return 1.0
    return difflib.SequenceMatcher(None, a, b, autojunk=False).ratio()


def main() -> None:
    parser = argparse.ArgumentParser(description="Profile the three unitary mass formula module families.")
    add_path_arguments(parser)
    src_root, db_path, out_dir = resolve_paths(parser.parse_args())
    out_json = out_dir / "unitary_clone_profile.json"

    import duckdb

    con = duckdb.connect(str(db_path), read_only=True)
    by_dir: dict[str, dict[str, dict]] = {}
    ns_counters: dict[str, Counter] = {d: Counter() for d in DIRS}

    for d in DIRS:
        rows = con.execute(
            """
            SELECT m.module, m.rel_path, m.lines, m.bytes, m.decl_count, r.depth_from_main, r.in_degree
            FROM modules m
            LEFT JOIN reachability r ON m.module = r.module
            WHERE m.module LIKE ? OR m.module = ?
            ORDER BY m.module
            """,
            [PREFIX + d + ".%", PREFIX + d],
        ).fetchall()
        mp = {}
        for mod, rel, lines, nbytes, decls, depth, indeg in rows:
            sub = mod[len(PREFIX + d) + 1 :] if mod.startswith(PREFIX + d + ".") else "<ROOT>"
            txt = (src_root / rel).read_text(encoding="utf-8", errors="replace")
            raw_lines = txt.splitlines()
            ns_list = detect_namespace_tags(raw_lines)
            for ns in ns_list:
                ns_counters[d][ns] += 1
            mp[sub] = {
                "module": mod,
                "rel_path": rel,
                "lines": len(raw_lines),
                "bytes": nbytes,
                "decls": decls,
                "depth": depth,
                "in_degree": indeg,
                "namespaces": ns_list,
                "raw_lines": raw_lines,
            }
        by_dir[d] = mp
    con.close()

    print("=== Namespace tags frequency per directory ===")
    for d in DIRS:
        print(f"  {d}: {ns_counters[d].most_common(10)}")

    # Detect dominant namespace prefix per dir for normalized comparison
    # Find tokens differing only by namespace prefix
    s1, s2, s3 = set(by_dir[DIRS[0]]), set(by_dir[DIRS[1]]), set(by_dir[DIRS[2]])
    triplets = sorted(s1 & s2 & s3)
    pairs_12 = sorted((s1 & s2) - s3)
    pairs_13 = sorted((s1 & s3) - s2)
    pairs_23 = sorted((s2 & s3) - s1)
    uniq = {
        DIRS[0]: sorted(s1 - s2 - s3),
        DIRS[1]: sorted(s2 - s1 - s3),
        DIRS[2]: sorted(s3 - s1 - s2),
    }

    # Build transparent per-dir namespace normalization map from most common namespace tag
    ns_maps: dict[str, dict[str, str]] = {}
    for d in DIRS:
        top_ns = ns_counters[d].most_common(1)[0][0] if ns_counters[d] else ""
        # Also detect short prefix like UnitaryOrbit / UnitaryStab / WeilStab if present
        ns_maps[d] = {top_ns: "<NS>"} if top_ns else {}

    triplet_records = []
    buckets = Counter()
    total_triplet_lines = [0, 0, 0]
    exact_raw_body_3 = 0
    exact_norm_body_3 = 0

    for name in triplets:
        r0, r1, r2 = by_dir[DIRS[0]][name], by_dir[DIRS[1]][name], by_dir[DIRS[2]][name]
        l0, l1, l2 = r0["lines"], r1["lines"], r2["lines"]
        total_triplet_lines[0] += l0
        total_triplet_lines[1] += l1
        total_triplet_lines[2] += l2

        b0 = strip_imports_and_ns(r0["raw_lines"])
        b1 = strip_imports_and_ns(r1["raw_lines"])
        b2 = strip_imports_and_ns(r2["raw_lines"])

        n0 = normalize_body(r0["raw_lines"], DIRS[0], ns_maps[DIRS[0]])
        n1 = normalize_body(r1["raw_lines"], DIRS[1], ns_maps[DIRS[1]])
        n2 = normalize_body(r2["raw_lines"], DIRS[2], ns_maps[DIRS[2]])

        raw_01 = pair_sim(b0, b1)
        raw_02 = pair_sim(b0, b2)
        raw_12 = pair_sim(b1, b2)
        raw_min = min(raw_01, raw_02, raw_12)
        raw_avg = (raw_01 + raw_02 + raw_12) / 3.0

        norm_01 = pair_sim(n0, n1)
        norm_02 = pair_sim(n0, n2)
        norm_12 = pair_sim(n1, n2)
        norm_min = min(norm_01, norm_02, norm_12)
        norm_avg = (norm_01 + norm_02 + norm_12) / 3.0

        if b0 == b1 == b2:
            exact_raw_body_3 += 1
        if n0 == n1 == n2:
            exact_norm_body_3 += 1

        if norm_min >= 0.999999:
            cat = "exact_100pct"
        elif norm_min >= 0.95:
            cat = "near_identical_95_99"
        elif norm_min >= 0.80:
            cat = "high_similar_80_95"
        elif norm_min >= 0.50:
            cat = "moderate_50_80"
        else:
            cat = "divergent_lt50"
        buckets[cat] += 1

        # Count diff lines (unified diff changed lines) between 0-1 and 0-2 on normalized bodies
        diff_01 = sum(1 for ln in difflib.unified_diff(n0, n1, n=0) if (ln.startswith("+") or ln.startswith("-")) and not ln.startswith("+++") and not ln.startswith("---"))
        diff_02 = sum(1 for ln in difflib.unified_diff(n0, n2, n=0) if (ln.startswith("+") or ln.startswith("-")) and not ln.startswith("+++") and not ln.startswith("---"))
        diff_12 = sum(1 for ln in difflib.unified_diff(n1, n2, n=0) if (ln.startswith("+") or ln.startswith("-")) and not ln.startswith("+++") and not ln.startswith("---"))

        triplet_records.append({
            "name": name,
            "lines": [l0, l1, l2],
            "sum_lines": l0 + l1 + l2,
            "max_lines": max(l0, l1, l2),
            "redundant_if_unified": (l0 + l1 + l2) - max(l0, l1, l2),
            "decls": [r0["decls"], r1["decls"], r2["decls"]],
            "raw_sims": [round(raw_01, 4), round(raw_02, 4), round(raw_12, 4)],
            "raw_min": round(raw_min, 4),
            "raw_avg": round(raw_avg, 4),
            "norm_sims": [round(norm_01, 4), round(norm_02, 4), round(norm_12, 4)],
            "norm_min": round(norm_min, 4),
            "norm_avg": round(norm_avg, 4),
            "diff_lines_norm": [diff_01, diff_02, diff_12],
            "category": cat,
            "namespaces": [r0["namespaces"], r1["namespaces"], r2["namespaces"]],
        })

    # Inspect exact diffs on divergent / non-identical triplets
    non_exact = [r for r in triplet_records if r["category"] != "exact_100pct"]
    non_exact.sort(key=lambda r: (r["norm_min"], -r["sum_lines"]))

    print(f"\n=== Summary ===")
    print(f"Triplets: {len(triplets)}, sum_lines={sum(total_triplet_lines)} ({total_triplet_lines})")
    print(f"Exact raw body match across all 3: {exact_raw_body_3} / {len(triplets)}")
    print(f"Exact norm body match across all 3: {exact_norm_body_3} / {len(triplets)}")
    print(f"Category breakdown: {dict(buckets)}")
    for cat in ["exact_100pct", "near_identical_95_99", "high_similar_80_95", "moderate_50_80", "divergent_lt50"]:
        sub = [r for r in triplet_records if r["category"] == cat]
        print(f"  {cat:22s}: {len(sub):3d} triplets, total_lines={sum(r['sum_lines'] for r in sub):6d}, redundant_2_copies={sum(r['redundant_if_unified'] for r in sub):6d}")

    print("\n=== Non-100%-exact triplets (sorted by norm_min asc) ===")
    for r in non_exact[:35]:
        print(f"  {r['name']:28s} L={r['lines']} norm_sims={r['norm_sims']} diff={r['diff_lines_norm']} cat={r['category']}")

    print("\n=== Largest 15 exact_100pct / near_identical triplets ===")
    for r in sorted(triplet_records, key=lambda x: -x["sum_lines"])[:15]:
        print(f"  {r['name']:28s} L={r['lines']} sum={r['sum_lines']:4d} norm_min={r['norm_min']:.4f} raw_min={r['raw_min']:.4f} diff={r['diff_lines_norm']}")

    # Inspect shared pairs
    pair_records = []
    for label, d_a, d_b, names in [
        ("Orbit_Stab", DIRS[0], DIRS[1], pairs_12),
        ("Orbit_Weil", DIRS[0], DIRS[2], pairs_13),
        ("Stab_Weil", DIRS[1], DIRS[2], pairs_23),
    ]:
        for name in names:
            ra, rb = by_dir[d_a][name], by_dir[d_b][name]
            na = normalize_body(ra["raw_lines"], d_a, ns_maps[d_a])
            nb = normalize_body(rb["raw_lines"], d_b, ns_maps[d_b])
            sim = pair_sim(na, nb)
            pair_records.append({
                "pair": label,
                "name": name,
                "lines": [ra["lines"], rb["lines"]],
                "norm_sim": round(sim, 4),
            })
    print("\n=== Shared pairs (2 of 3) ===")
    for pr in pair_records:
        print(" ", pr)

    uniq_summary = {}
    print("\n=== Unique files per directory ===")
    for d in DIRS:
        items = [{"name": n, "lines": by_dir[d][n]["lines"], "decls": by_dir[d][n]["decls"]} for n in uniq[d]]
        uniq_summary[d] = items
        print(f"  {d} ({len(items)} files, {sum(x['lines'] for x in items)}L): {items}")

    # External importers of each directory
    con = duckdb.connect(str(db_path), read_only=True)
    ext_importers = {}
    for d in DIRS:
        pref = PREFIX + d
        rows = con.execute(
            """
            SELECT DISTINCT src_module, dst_module
            FROM imports
            WHERE (dst_module LIKE ? OR dst_module = ?)
              AND NOT (src_module LIKE ? OR src_module = ?)
            ORDER BY src_module, dst_module
            """,
            [pref + ".%", pref, pref + ".%", pref],
        ).fetchall()
        ext_importers[d] = rows
        print(f"\n=== External importers of {d}: {len(rows)} edges ===")
        for s, t in rows[:20]:
            print(f"  {s} -> {t}")
    con.close()

    # Check total lines summary
    dir_totals = {
        d: {
            "modules": len(by_dir[d]),
            "lines": sum(x["lines"] for x in by_dir[d].values()),
            "bytes": sum(x["bytes"] for x in by_dir[d].values()),
            "top_namespaces": ns_counters[d].most_common(5),
        }
        for d in DIRS
    }

    payload = {
        "dir_totals": dir_totals,
        "triplet_count": len(triplets),
        "exact_raw_body_3": exact_raw_body_3,
        "exact_norm_body_3": exact_norm_body_3,
        "category_counts": dict(buckets),
        "triplets": triplet_records,
        "pairs": pair_records,
        "unique_files": uniq_summary,
        "external_importers": ext_importers,
    }
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"\nWrote profile JSON -> {out_json}")


if __name__ == "__main__":
    main()

