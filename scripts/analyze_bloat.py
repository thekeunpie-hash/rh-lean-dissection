#!/usr/bin/env python3
"""
Track C: Comprehensive Bloat, Redundancy, Mathlib-Replaceable & Subtree Cone Analyzer
for the 175,187-module (17.37M-line) Lean 4.33.1 codebase.

Runs ONE parallel file pass across all 175,187 files (16 workers) + DuckDB DAG/cone analysis.
Writes structured JSON to teamwork_out/bloat_analysis_data.json.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import time
from collections import Counter, defaultdict, deque
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

from index_lean import add_path_arguments, resolve_paths


# Regexes matching index_lean.py for consistent decl boundaries
RE_IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?import\s+([A-Za-z0-9_.'`]+)")
RE_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|axiom|structure|class|inductive|opaque|instance)\b(?:\s+([^\s:({\[=]+))?"
)
RE_BOILERPLATE_LINE = re.compile(
    r"^(?:(?:public|private)\s+)?(?:import|namespace|end|open|section|set_option|noncomputable\s+section|variable|universe|attribute|local\s+attribute)\b"
)
# Explicit @ application (excluding @[ attribute syntax)
RE_EXPLICIT_AT = re.compile(r"(?:^|[\s(\[{])@[A-Za-z_]")
# Project namespace normalization: collapse project-specific prefixes to <P>.tail
RE_PROJ_PREFIX = re.compile(
    r"\b(?:_root_\.)?(?:Development|Formalism|GroundTheory|ReciprocityTheory|CompanionTheory|PositivityTheory|UpperTheory|GlobalTheory|Lemmata|Supplements|BuildAid)(?:\.[A-Za-z0-9_']+)+\.([A-Za-z_][A-Za-z0-9_']*)"
)
RE_DIGITS_IN_IDENT = re.compile(r"(?<=[A-Za-z_])[0-9]+")
RE_NUM_LIT = re.compile(r"\b[0-9]+\b")
RE_WS = re.compile(r"\s+")

TACTIC_HEADS = {
    "have", "let", "letI", "set", "obtain", "rcases", "rintro", "intro", "intros",
    "rw", "erw", "rwa", "simp", "simp_all", "dsimp", "simpa", "exact", "apply",
    "refine", "refine'", "use", "exists", "constructor", "left", "right",
    "cases", "rcases", "induction", "by_cases", "by_contra", "by_contradiction",
    "ext", "funext", "congr", "convert", "calc", "show", "change", "unfold",
    "delta", "subst", "clear", "rename_i", "specialize", "generalize",
    "ring", "ring_nf", "linarith", "nlinarith", "omega", "positivity", "polyrith",
    "field_simp", "norm_num", "norm_cast", "push_cast", "exact_mod_cast",
    "push_neg", "contrapose", "aesop", "tauto", "decide", "rfl", "trivial",
    "contradiction", "exfalso", "abel", "group", "module", "continuity",
    "measurability", "fun_prop", "grind", "classical", "infer_instance",
    "conv", "conv_lhs", "conv_rhs", "nth_rw", "swap", "rotate_left", "rotate_right",
    "·", "|", "case", "all_goals", "any_goals", "try", "repeat", "first", "done",
    "suffices", "assert", "trans", "calc", "gcongr", "bound", "filter_upwards",
    "fconstructor", "econstructor", "injection", "revert", "split_ifs", "fin_cases",
    "interval_cases", "match", "if", "for", "do",
}


def h64(s: str) -> int:
    return int.from_bytes(hashlib.blake2b(s.encode("utf-8", errors="ignore"), digest_size=8).digest(), "little")


def normalize_line(s: str) -> str:
    s = RE_PROJ_PREFIX.sub(r"<P>.\1", s)
    s = RE_DIGITS_IN_IDENT.sub("#", s)
    s = RE_NUM_LIT.sub("#", s)
    s = RE_WS.sub(" ", s).strip()
    return s


def tactic_token(line_raw: str, stripped: str) -> str:
    indent = len(line_raw) - len(line_raw.lstrip(" "))
    ibucket = min(indent // 2, 12)
    tok = stripped.split(None, 1)[0] if stripped else ""
    if tok.startswith("·"):
        tok = "·"
    elif tok.startswith("|"):
        tok = "|"
    else:
        tok = tok.rstrip("[,:;")
    if tok in TACTIC_HEADS:
        return f"{ibucket}:{tok}"
    return f"{ibucket}:_"


def strip_comments_lines(lines: list[str]) -> list[tuple[int, str, str]]:
    """Return list of (1-based line_no, raw_code_without_comments, stripped_code)."""
    out: list[tuple[int, str, str]] = []
    in_block = 0
    for idx, line in enumerate(lines, start=1):
        s = line
        if "/-" in s or "-/" in s or in_block > 0:
            chars = []
            i = 0
            n = len(s)
            while i < n:
                if s[i : i + 2] == "/-":
                    in_block += 1
                    i += 2
                elif s[i : i + 2] == "-/" and in_block > 0:
                    in_block -= 1
                    i += 2
                else:
                    if in_block == 0:
                        chars.append(s[i])
                    i += 1
            s = "".join(chars)
        cidx = s.find("--")
        code = s[:cidx] if cidx != -1 else s
        out.append((idx, code, code.strip()))
    return out


def process_batch(args: tuple[str, list[tuple[str, str, int]]]) -> dict:
    """
    Process a batch of (module, rel_path, reachable_int).
    Returns compact aggregated stats + candidate lists to minimize IPC overhead.
    """
    src_root = Path(args[0])
    items = args[1]

    # Per-batch accumulators
    file_stats = {
        "files": 0,
        "reach_files": 0,
        "total_lines": 0,
        "reach_lines": 0,
        "code_lines": 0,
        "reach_code_lines": 0,
        "explicit_at_lines": 0,
        "reach_explicit_at_lines": 0,
        "heavy_explicit_files": 0,
        "heavy_explicit_lines": 0,
        "intra_dup_lines_6": 0,
        "reach_intra_dup_lines_6": 0,
        "sig_lines_total": 0,
        "body_lines_total": 0,
        "tactic_decls": 0,
        "tactic_body_lines": 0,
    }

    # Detailed lists (kept compact!)
    # File hashes: (exact_hash, norm_hash, mod, lines, code_lines, reachable)
    file_hashes: list[tuple[int, int, str, int, int, int]] = []
    # Decl hashes for span >= 8 (only reachable or all, tag reachable)
    # (norm_decl_h, exact_body_h, norm_body_h, skel_h, mod, name, kind, start_ln, span, sig_lns, body_lns, at_sig, at_body, is_tac, reach)
    decl_records: list[tuple] = []
    # Large declarations (span >= 150 or body_lines >= 120) for Top-N tables
    large_decls: list[tuple] = []
    # Explicit-heavy files (at_lines >= 50)
    heavy_at_files: list[tuple[str, int, int, int]] = []
    compression_targets: list[dict] = []
    # Non-overlapping declaration-aligned 6-line normalized blocks (hash -> count, only reachable)
    # Also track total reachable block-covered lines
    block6_counts: Counter[int] = Counter()
    block6_examples: dict[int, tuple[str, int, str]] = {}
    reach_block6_total_blocks = 0

    for mod, rel, reach in items:
        full_path = src_root / rel
        try:
            raw = full_path.read_bytes()
        except OSError:
            continue
        text = raw.decode("utf-8", errors="replace")
        lines = text.splitlines()
        n_lines = len(lines)
        cleaned = strip_comments_lines(lines)

        file_stats["files"] += 1
        file_stats["total_lines"] += n_lines
        if reach:
            file_stats["reach_files"] += 1
            file_stats["reach_lines"] += n_lines

        code_lines_list: list[tuple[int, str, str]] = []
        content_exact: list[str] = []
        content_norm: list[str] = []
        file_at_lines = 0

        # Parse declarations matching index_lean.py
        decls_raw: list[list] = []  # [kind, name, start_idx_in_lines(1-based)]
        for ln, code, stripped in cleaned:
            if not stripped:
                continue
            code_lines_list.append((ln, code, stripped))
            if RE_EXPLICIT_AT.search(code):
                file_at_lines += 1
            if not RE_BOILERPLATE_LINE.match(stripped):
                content_exact.append(RE_WS.sub(" ", stripped))
                content_norm.append(normalize_line(stripped))
            if not code[0].isspace() or code.startswith("  "):
                m_decl = RE_DECL.match(code)
                if m_decl:
                    decls_raw.append([m_decl.group(1), m_decl.group(2) or "<anonymous>", ln])

        n_code = len(code_lines_list)
        file_stats["code_lines"] += n_code
        file_stats["explicit_at_lines"] += file_at_lines
        if reach:
            file_stats["reach_code_lines"] += n_code
            file_stats["reach_explicit_at_lines"] += file_at_lines

        if reach and file_at_lines >= 20 and (file_at_lines / max(1, n_code)) >= 0.15:
            file_stats["heavy_explicit_files"] += 1
            file_stats["heavy_explicit_lines"] += n_lines
            compression_targets.append({
                "module": mod,
                "rel_path": rel.replace("\\", "/"),
                "lines": n_lines,
                "code_lines": n_code,
                "explicit_at_lines": file_at_lines,
                "is_capelli": mod.startswith("Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities."),
            })
        if reach and file_at_lines >= 50:
            heavy_at_files.append((mod, n_lines, file_at_lines, n_code))

        # Intra-file 6-line sliding window duplicate line count (normalized non-boilerplate lines)
        m_cnt = len(content_norm)
        if m_cnt >= 12:
            win_pos: dict[int, list[int]] = defaultdict(list)
            for i in range(m_cnt - 5):
                wh = h64("\n".join(content_norm[i : i + 6]))
                win_pos[wh].append(i)
            covered = bytearray(m_cnt)
            for positions in win_pos.values():
                if len(positions) >= 2:
                    # Keep first occurrence as canonical; mark subsequent occurrences as duplicate
                    for p in positions[1:]:
                        for k in range(p, p + 6):
                            covered[k] = 1
            # Don't count positions already overlapping first occurrence? Actually marking subsequent
            # occurrences that don't overlap the canonical first copy is even cleaner:
            # Recompute cleanly:
            dup_mask = bytearray(m_cnt)
            for positions in win_pos.values():
                if len(positions) >= 2:
                    first = positions[0]
                    for p in positions[1:]:
                        if p >= first + 6:
                            for k in range(p, p + 6):
                                dup_mask[k] = 1
            intra_dups = sum(dup_mask)
            file_stats["intra_dup_lines_6"] += intra_dups
            if reach:
                file_stats["reach_intra_dup_lines_6"] += intra_dups

        # Whole-file hashes (only for files with >= 8 content lines)
        if m_cnt >= 8:
            fe_h = h64("\n".join(content_exact))
            fn_h = h64("\n".join(content_norm))
            file_hashes.append((fe_h, fn_h, mod, n_lines, m_cnt, reach))

        # Process declarations
        for i, d in enumerate(decls_raw):
            kind, name, start_ln = d
            end_ln = (decls_raw[i + 1][2] - 1) if (i + 1 < len(decls_raw)) else n_lines
            span = max(1, end_ln - start_ln + 1)

            # Find split between signature and body (first top-level `:=` or `where`)
            sig_end_ln = end_ln
            is_tac = 0
            found_split = False
            at_sig = 0
            at_body = 0
            body_exact_lines: list[str] = []
            body_norm_lines: list[str] = []
            decl_norm_lines: list[str] = []
            skel_tokens: list[str] = []

            for ln_idx in range(start_ln - 1, end_ln):
                ln_no, code, stripped = cleaned[ln_idx]
                if not stripped:
                    continue
                has_at = 1 if RE_EXPLICIT_AT.search(code) else 0
                if not found_split:
                    # Normalize header line without decl name
                    if ln_no == start_ln:
                        hdr = stripped.replace(name, "<DECL>", 1)
                        decl_norm_lines.append(normalize_line(hdr))
                    else:
                        decl_norm_lines.append(normalize_line(stripped))
                    if ":=" in stripped:
                        found_split = True
                        sig_end_ln = ln_no
                        before, after = stripped.split(":=", 1)
                        if RE_EXPLICIT_AT.search(before):
                            at_sig += 1
                        after_s = after.strip()
                        if after_s == "by" or after_s.startswith("by "):
                            is_tac = 1
                            rest = after_s[2:].strip()
                            if rest:
                                body_exact_lines.append(RE_WS.sub(" ", rest))
                                body_norm_lines.append(normalize_line(rest))
                                skel_tokens.append(tactic_token(code, rest))
                        elif after_s:
                            if RE_EXPLICIT_AT.search(after_s):
                                at_body += 1
                            body_exact_lines.append(RE_WS.sub(" ", after_s))
                            body_norm_lines.append(normalize_line(after_s))
                    elif kind in ("structure", "class", "inductive", "instance") and (
                        stripped == "where" or stripped.endswith(" where") or stripped.startswith("where ")
                    ):
                        found_split = True
                        sig_end_ln = ln_no
                        if has_at:
                            at_sig += 1
                    else:
                        if has_at:
                            at_sig += 1
                else:
                    if has_at:
                        at_body += 1
                    nl = normalize_line(stripped)
                    decl_norm_lines.append(nl)
                    if not body_exact_lines and (stripped == "by" or stripped.startswith("by ")):
                        is_tac = 1
                        rest = stripped[2:].strip()
                        if rest:
                            body_exact_lines.append(RE_WS.sub(" ", rest))
                            body_norm_lines.append(normalize_line(rest))
                            skel_tokens.append(tactic_token(code, rest))
                    else:
                        body_exact_lines.append(RE_WS.sub(" ", stripped))
                        body_norm_lines.append(nl)
                        if is_tac:
                            skel_tokens.append(tactic_token(code, stripped))

            sig_lns = (sig_end_ln - start_ln + 1) if found_split else span
            body_lns = max(0, span - sig_lns)

            if reach:
                file_stats["sig_lines_total"] += sig_lns
                file_stats["body_lines_total"] += body_lns
                if is_tac:
                    file_stats["tactic_decls"] += 1
                    file_stats["tactic_body_lines"] += body_lns

                # Declaration-aligned non-overlapping 6-line normalized blocks (for cross-file dedup)
                n_dn = len(decl_norm_lines)
                if n_dn >= 6:
                    for bi in range(0, n_dn - 5, 6):
                        chunk = "\n".join(decl_norm_lines[bi : bi + 6])
                        bh = h64(chunk)
                        block6_counts[bh] += 1
                        reach_block6_total_blocks += 1
                        if bh not in block6_examples:
                            block6_examples[bh] = (mod, start_ln, decl_norm_lines[bi][:120])

            if reach and (span >= 150 or body_lns >= 120):
                large_decls.append(
                    (span, sig_lns, body_lns, at_sig, at_body, is_tac, kind, mod, name, start_ln, end_ln)
                )

            if reach and span >= 10:
                nd_h = h64("\n".join(decl_norm_lines)) if decl_norm_lines else 0
                eb_h = h64("\n".join(body_exact_lines)) if len(body_exact_lines) >= 6 else 0
                nb_h = h64("\n".join(body_norm_lines)) if len(body_norm_lines) >= 6 else 0
                sk_h = h64("|".join(skel_tokens)) if (is_tac and len(skel_tokens) >= 12) else 0
                decl_records.append(
                    (nd_h, eb_h, nb_h, sk_h, mod, name, kind, start_ln, span, sig_lns, body_lns, at_sig, at_body, is_tac)
                )

    return {
        "file_stats": file_stats,
        "file_hashes": file_hashes,
        "decl_records": decl_records,
        "large_decls": large_decls,
        "heavy_at_files": heavy_at_files,
        "compression_targets": compression_targets,
        "block6_counts": block6_counts,
        "block6_examples": block6_examples,
        "reach_block6_total_blocks": reach_block6_total_blocks,
    }


def compute_cones(
    seed_mods: set[str],
    reach_mods: set[str],
    adj_fwd: dict[str, list[str]],
    adj_rev: dict[str, list[str]],
    mod_lines: dict[str, int],
    mod_depth: dict[str, int],
) -> dict:
    """
    Compute:
      - direct: seed_mods ∩ reach_mods
      - downstream_cone: all reachable modules transitively imported by seed_mods (incl. seed_mods)
      - upstream_cone: all reachable modules that transitively import seed_mods (incl. seed_mods)
      - exclusive_cone: R_Main \ Reach(Main, G \ seed_mods) — modules that become unreachable from Main if seed_mods are removed!
      - strict_exclusive_downstream: exclusive_cone \ seed_mods
      - direct_importers: reachable modules outside seed_mods that directly import some module in seed_mods
    """
    S = seed_mods & reach_mods
    if not S:
        return {
            "direct_mods": 0,
            "direct_lines": 0,
            "downstream_mods": 0,
            "downstream_lines": 0,
            "exclusive_mods": 0,
            "exclusive_lines": 0,
            "strict_exclusive_downstream_mods": 0,
            "strict_exclusive_downstream_lines": 0,
            "upstream_mods": 0,
            "upstream_lines": 0,
            "direct_importers_count": 0,
            "min_depth": None,
            "sample_importers": [],
        }

    # Downstream BFS from S
    down = set(S)
    q = deque(S)
    while q:
        u = q.popleft()
        for v in adj_fwd.get(u, ()):
            if v in reach_mods and v not in down:
                down.add(v)
                q.append(v)

    # Upstream BFS from S
    up = set(S)
    q = deque(S)
    while q:
        u = q.popleft()
        for p in adj_rev.get(u, ()):
            if p in reach_mods and p not in up:
                up.add(p)
                q.append(p)

    # Exclusive cone: BFS from Main avoiding S
    reach_without_S: set[str] = set()
    if "Main" in reach_mods and "Main" not in S:
        reach_without_S.add("Main")
        q = deque(["Main"])
        while q:
            u = q.popleft()
            for v in adj_fwd.get(u, ()):
                if v in reach_mods and v not in S and v not in reach_without_S:
                    reach_without_S.add(v)
                    q.append(v)
    excl = reach_mods - reach_without_S
    strict_excl = excl - S

    direct_importers = set()
    for s in S:
        for p in adj_rev.get(s, ()):
            if p in reach_mods and p not in S:
                direct_importers.add(p)

    sorted_importers = sorted(direct_importers, key=lambda m: (mod_depth.get(m, 999), m))
    min_depth = min(mod_depth.get(m, 999) for m in S)

    return {
        "direct_mods": len(S),
        "direct_lines": sum(mod_lines[m] for m in S),
        "downstream_mods": len(down),
        "downstream_lines": sum(mod_lines[m] for m in down),
        "exclusive_mods": len(excl),
        "exclusive_lines": sum(mod_lines[m] for m in excl),
        "strict_exclusive_downstream_mods": len(strict_excl),
        "strict_exclusive_downstream_lines": sum(mod_lines[m] for m in strict_excl),
        "upstream_mods": len(up),
        "upstream_lines": sum(mod_lines[m] for m in up),
        "direct_importers_count": len(direct_importers),
        "min_depth": min_depth,
        "sample_importers": [(m, mod_depth.get(m, -1), mod_lines[m]) for m in sorted_importers[:15]],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Profile explicit syntax, duplicates, and import cones.")
    add_path_arguments(parser)
    src_root, db_path, out_dir = resolve_paths(parser.parse_args())
    out_json = out_dir / "bloat_analysis_data.json"

    import duckdb

    t0 = time.perf_counter()
    out_dir.mkdir(parents=True, exist_ok=True)
    con = duckdb.connect(str(db_path), read_only=True)

    print("[1/5] Loading module metadata & import DAG from DuckDB ...", flush=True)
    mod_rows = con.execute(
        """
        SELECT m.module, m.rel_path, m.lines, m.has_mathlib_import, m.top_lib, m.decl_count,
               r.reachable, r.depth_from_main, r.in_degree, r.local_out_degree
        FROM modules m
        JOIN reachability r USING (module)
        """
    ).fetchall()

    mod_lines: dict[str, int] = {}
    mod_depth: dict[str, int] = {}
    mod_indeg: dict[str, int] = {}
    mod_mathlib: dict[str, bool] = {}
    mod_toplib: dict[str, str] = {}
    reach_mods: set[str] = set()
    all_mods: set[str] = set()
    batch_items: list[tuple[str, str, int]] = []

    for mod, rel, lines, has_ml, tlib, dcnt, rch, dep, indeg, outdeg in mod_rows:
        all_mods.add(mod)
        mod_lines[mod] = lines
        mod_depth[mod] = dep
        mod_indeg[mod] = indeg
        mod_mathlib[mod] = bool(has_ml)
        mod_toplib[mod] = tlib
        if rch:
            reach_mods.add(mod)
        batch_items.append((mod, rel, 1 if rch else 0))

    total_lines_all = sum(mod_lines.values())
    reach_lines_all = sum(mod_lines[m] for m in reach_mods)
    dead_mods = all_mods - reach_mods
    dead_lines = total_lines_all - reach_lines_all

    # Load imports
    adj_fwd: dict[str, list[str]] = defaultdict(list)
    adj_rev: dict[str, list[str]] = defaultdict(list)
    imp_rows = con.execute("SELECT src_module, dst_module FROM imports").fetchall()
    for src, dst in imp_rows:
        if dst in all_mods:
            adj_fwd[src].append(dst)
            adj_rev[dst].append(src)
    del imp_rows

    print(
        f"      Loaded {len(all_mods):,} mods ({len(reach_mods):,} reachable, {reach_lines_all:,} lines) in {time.perf_counter()-t0:.2f}s",
        flush=True,
    )

    # [2/5] Parallel structural fingerprinting pass
    t1 = time.perf_counter()
    workers = max(1, min(os.cpu_count() or 8, 16))
    batch_size = 1500
    batches = [
        (str(src_root), batch_items[i : i + batch_size])
        for i in range(0, len(batch_items), batch_size)
    ]
    print(f"[2/5] Parallel structural fingerprinting ({len(batch_items):,} files, {workers} workers) ...", flush=True)

    agg_stats = Counter()
    all_file_hashes: list[tuple[int, int, str, int, int, int]] = []
    all_decl_records: list[tuple] = []
    all_large_decls: list[tuple] = []
    all_heavy_at_files: list[tuple[str, int, int, int]] = []
    compression_targets: list[dict] = []
    global_block6_counts: Counter[int] = Counter()
    global_block6_examples: dict[int, tuple[str, int, str]] = {}
    total_reach_blocks = 0

    done = 0
    with ProcessPoolExecutor(max_workers=workers) as ex:
        for res in ex.map(process_batch, batches):
            for k, v in res["file_stats"].items():
                agg_stats[k] += v
            all_file_hashes.extend(res["file_hashes"])
            all_decl_records.extend(res["decl_records"])
            all_large_decls.extend(res["large_decls"])
            all_heavy_at_files.extend(res["heavy_at_files"])
            compression_targets.extend(res["compression_targets"])
            global_block6_counts.update(res["block6_counts"])
            for bh, ex_val in res["block6_examples"].items():
                if bh not in global_block6_examples:
                    global_block6_examples[bh] = ex_val
            total_reach_blocks += res["reach_block6_total_blocks"]
            done += res["file_stats"]["files"]
            if done % 30000 < batch_size or done == len(batch_items):
                print(f"      Fingerprinted {done:,} / {len(batch_items):,} ({time.perf_counter()-t1:.1f}s)", flush=True)

    t2 = time.perf_counter()
    print(f"[3/5] Clustering duplicates & ranking targets ({t2-t1:.2f}s scan) ...", flush=True)

    # --- 1(a) Top 30 Longest Single Declarations ---
    # Overall Top 30 (reachable)
    all_large_decls.sort(key=lambda x: (-x[0], x[7], x[9]))
    top30_overall = [
        {
            "rank": idx + 1,
            "span_lines": x[0],
            "sig_lines": x[1],
            "body_lines": x[2],
            "at_sig_lines": x[3],
            "at_body_lines": x[4],
            "is_tactic_proof": bool(x[5]),
            "kind": x[6],
            "module": x[7],
            "name": x[8],
            "start_line": x[9],
            "end_line": x[10],
            "depth": mod_depth.get(x[7], -1),
        }
        for idx, x in enumerate(all_large_decls[:30])
    ]

    # Top 30 Theorems/Lemmas (reachable)
    thm_large = [x for x in all_large_decls if x[6] in ("theorem", "lemma")]
    top30_theorems = [
        {
            "rank": idx + 1,
            "span_lines": x[0],
            "sig_lines": x[1],
            "body_lines": x[2],
            "at_sig_lines": x[3],
            "at_body_lines": x[4],
            "is_tactic_proof": bool(x[5]),
            "kind": x[6],
            "module": x[7],
            "name": x[8],
            "start_line": x[9],
            "end_line": x[10],
            "depth": mod_depth.get(x[7], -1),
        }
        for idx, x in enumerate(thm_large[:30])
    ]

    # Top 30 Real Tactic Proof Bodies (ranked by body_lines where is_tactic_proof=True)
    tac_large = [x for x in all_large_decls if x[5] == 1 and x[6] in ("theorem", "lemma")]
    tac_large.sort(key=lambda x: (-x[2], -x[0], x[7]))
    top30_tactic_bodies = [
        {
            "rank": idx + 1,
            "body_lines": x[2],
            "sig_lines": x[1],
            "span_lines": x[0],
            "at_sig_lines": x[3],
            "kind": x[6],
            "module": x[7],
            "name": x[8],
            "start_line": x[9],
            "end_line": x[10],
            "depth": mod_depth.get(x[7], -1),
        }
        for idx, x in enumerate(tac_large[:30])
    ]

    # --- 1(b) Duplicate Clusters ---
    # 1. Whole-file exact & normalized duplicates (reachable)
    file_exact_groups: dict[int, list] = defaultdict(list)
    file_norm_groups: dict[int, list] = defaultdict(list)
    for fe_h, fn_h, mod, lns, m_cnt, rch in all_file_hashes:
        if rch:
            file_exact_groups[fe_h].append((mod, lns, m_cnt))
            file_norm_groups[fn_h].append((mod, lns, m_cnt))

    def summarize_file_groups(groups: dict[int, list]) -> tuple[dict, list]:
        dup_clusters = []
        total_dup_files = 0
        total_redundant_files = 0
        total_redundant_lines = 0
        for h, members in groups.items():
            if len(members) >= 2:
                members.sort(key=lambda x: (-x[1], x[0]))
                sum_l = sum(x[1] for x in members)
                red_l = sum_l - members[0][1]
                total_dup_files += len(members)
                total_redundant_files += len(members) - 1
                total_redundant_lines += red_l
                dup_clusters.append(
                    {
                        "count": len(members),
                        "avg_lines": round(sum_l / len(members), 1),
                        "total_lines": sum_l,
                        "redundant_lines": red_l,
                        "sample_modules": [x[0] for x in members[:6]],
                        "sample_lines": [x[1] for x in members[:6]],
                    }
                )
        dup_clusters.sort(key=lambda x: (-x["redundant_lines"], -x["count"]))
        summary = {
            "cluster_count": len(dup_clusters),
            "files_in_clusters": total_dup_files,
            "redundant_files": total_redundant_files,
            "redundant_lines": total_redundant_lines,
        }
        return summary, dup_clusters[:25]

    file_exact_summary, top_file_exact = summarize_file_groups(file_exact_groups)
    file_norm_summary, top_file_norm = summarize_file_groups(file_norm_groups)

    # 2. Declaration-level clusters (reachable, span >= 10)
    # record: (nd_h, eb_h, nb_h, sk_h, mod, name, kind, start_ln, span, sig_lns, body_lns, at_sig, at_body, is_tac)
    decl_norm_groups: dict[int, list] = defaultdict(list)
    body_exact_groups: dict[int, list] = defaultdict(list)
    body_norm_groups: dict[int, list] = defaultdict(list)
    skel_groups: dict[int, list] = defaultdict(list)

    for rec in all_decl_records:
        nd_h, eb_h, nb_h, sk_h = rec[0], rec[1], rec[2], rec[3]
        if nd_h:
            decl_norm_groups[nd_h].append(rec)
        if eb_h:
            body_exact_groups[eb_h].append(rec)
        if nb_h:
            body_norm_groups[nb_h].append(rec)
        if sk_h:
            skel_groups[sk_h].append(rec)

    def summarize_decl_groups(groups: dict[int, list], use_body_lines: bool = False) -> tuple[dict, list]:
        clusters = []
        tot_decls = 0
        tot_red_decls = 0
        tot_red_lines = 0
        for h, mems in groups.items():
            if len(mems) >= 2:
                metric = (lambda r: r[10]) if use_body_lines else (lambda r: r[8])
                mems.sort(key=lambda r: (-metric(r), r[4], r[7]))
                sum_l = sum(metric(r) for r in mems)
                red_l = sum_l - metric(mems[0])
                if red_l <= 0:
                    continue
                tot_decls += len(mems)
                tot_red_decls += len(mems) - 1
                tot_red_lines += red_l
                clusters.append(
                    {
                        "count": len(mems),
                        "distinct_modules": len({r[4] for r in mems}),
                        "avg_lines": round(sum_l / len(mems), 1),
                        "total_lines": sum_l,
                        "redundant_lines": red_l,
                        "kind": mems[0][6],
                        "is_tactic": bool(mems[0][13]),
                        "sample_decls": [f"{r[4]}::{r[5]} (L{r[7]}, {r[8]}L/body {r[10]}L)" for r in mems[:6]],
                    }
                )
        clusters.sort(key=lambda x: (-x["redundant_lines"], -x["count"]))
        summary = {
            "cluster_count": len(clusters),
            "decls_in_clusters": tot_decls,
            "redundant_decls": tot_red_decls,
            "redundant_lines": tot_red_lines,
        }
        return summary, clusters[:25]

    decl_norm_summary, top_decl_norm = summarize_decl_groups(decl_norm_groups, use_body_lines=False)
    body_exact_summary, top_body_exact = summarize_decl_groups(body_exact_groups, use_body_lines=True)
    body_norm_summary, top_body_norm = summarize_decl_groups(body_norm_groups, use_body_lines=True)
    skel_summary, top_skel = summarize_decl_groups(skel_groups, use_body_lines=True)

    # 3. Block-level (6-line normalized decl-aligned chunks) redundancy across ALL reachable files
    dup_block_unique = 0
    redundant_block_occurrences = 0
    top_blocks = []
    for bh, cnt in global_block6_counts.items():
        if cnt >= 2:
            dup_block_unique += 1
            redundant_block_occurrences += cnt - 1
    for bh, cnt in global_block6_counts.most_common(25):
        if cnt >= 2:
            ex_m, ex_ln, ex_snip = global_block6_examples[bh]
            top_blocks.append(
                {
                    "occurrences": cnt,
                    "redundant_lines_est": (cnt - 1) * 6,
                    "sample_module": ex_m,
                    "sample_line": ex_ln,
                    "first_line_norm": ex_snip,
                }
            )
    block6_summary = {
        "total_6line_blocks_scanned": total_reach_blocks,
        "total_lines_in_blocks": total_reach_blocks * 6,
        "unique_duplicated_blocks": dup_block_unique,
        "redundant_block_occurrences": redundant_block_occurrences,
        "redundant_lines_block6": redundant_block_occurrences * 6,
        "pct_of_reachable_lines": round(100.0 * (redundant_block_occurrences * 6) / reach_lines_all, 2),
        "pct_of_total_lines": round(100.0 * (redundant_block_occurrences * 6) / total_lines_all, 2),
        "top_blocks": top_blocks,
    }

    # 4. Sibling Naming Patterns & Same-Span Pairs in DuckDB
    # Check specific Capelli/UpperTheory sibling namespaces + general same-tail-name same-span pairs
    sibling_same_span = con.execute(
        """
        WITH rdecls AS (
            SELECT d.module, d.kind, d.name, d.start_line, d.span_lines,
                   regexp_extract(d.name, '([^.]+)$', 1) AS tail_name
            FROM decls d JOIN reachability r USING (module)
            WHERE r.reachable AND d.span_lines >= 30
        )
        SELECT tail_name, span_lines, COUNT(*) AS cnt, COUNT(DISTINCT module) AS n_mods,
               SUM(span_lines) - MAX(span_lines) AS red_lines,
               list(module || '::' || name ORDER BY module)[1:5] AS samples
        FROM rdecls
        WHERE tail_name NOT IN ('<anonymous>', 'aux', 'aux1', 'aux2', 'aux3', 'aux4', 'main')
        GROUP BY tail_name, span_lines
        HAVING COUNT(*) >= 2 AND COUNT(DISTINCT module) >= 2
        ORDER BY red_lines DESC, cnt DESC
        LIMIT 30
        """
    ).fetchall()

    # Sibling numbered module clusters (strip digits from module name)
    sibling_mod_families = con.execute(
        """
        WITH rmods AS (
            SELECT m.module, m.lines,
                   regexp_replace(m.module, '[0-9]+', '#', 'g') AS pattern
            FROM modules m JOIN reachability r USING (module)
            WHERE r.reachable AND m.lines >= 20
        )
        SELECT pattern, COUNT(*) AS cnt, SUM(lines) AS tot_lines,
               MIN(lines) AS min_l, MAX(lines) AS max_l,
               list(module ORDER BY module)[1:5] AS samples
        FROM rmods
        WHERE pattern LIKE '%#%'
        GROUP BY pattern
        HAVING COUNT(*) >= 2
        ORDER BY tot_lines DESC
        LIMIT 25
        """
    ).fetchall()

    # CapelliIdentities / UpperTheory.Reformulated.B prefix breakdown
    capelli_prefixes = con.execute(
        """
        SELECT regexp_extract(d.name, '^(UpperTheory\\.Reformulated\\.B\\.[^.]+)', 1) AS ns_tag,
               COUNT(*) AS decls,
               COUNT(DISTINCT d.module) AS mods,
               SUM(d.span_lines) AS sum_span,
               MAX(d.span_lines) AS max_span,
               list(DISTINCT d.module)[1:3] AS sample_mods
        FROM decls d JOIN reachability r USING (module)
        WHERE r.reachable AND d.name LIKE 'UpperTheory.Reformulated.B.%'
        GROUP BY 1
        ORDER BY sum_span DESC
        LIMIT 30
        """
    ).fetchall()

    # Heavy explicit-@ files top 25
    all_heavy_at_files.sort(key=lambda x: (-x[2], -x[1]))
    top_heavy_at_files = [
        {"module": x[0], "total_lines": x[1], "explicit_at_lines": x[2], "code_lines": x[3], "at_ratio_pct": round(100.0 * x[2] / max(1, x[3]), 1)}
        for x in all_heavy_at_files[:25]
    ]

    # --- 1(c) Mathlib-Replaceable Foundational Reimplementation Candidates ---
    t3 = time.perf_counter()
    print(f"[4/5] Analyzing Mathlib-replaceable clusters & Behrend/Iwasawa cones ({t3-t2:.2f}s) ...", flush=True)

    # Compute transitive Mathlib dependency (reverse BFS from all modules that directly import Mathlib)
    trans_mathlib: set[str] = {m for m in all_mods if mod_mathlib[m]}
    q = deque(trans_mathlib)
    while q:
        u = q.popleft()
        for p in adj_rev.get(u, ()):
            if p not in trans_mathlib:
                trans_mathlib.add(p)
                q.append(p)

    pure_no_trans_mathlib = reach_mods - trans_mathlib

    # Breakdown by (top_lib, 2nd_level) for ALL reachable libraries + special focus on GroundTheory, Formalism, Lemmata, BuildAid, Development.EtaleCohomology, etc.
    lib2_stats: dict[tuple[str, str], dict] = {}
    for m in reach_mods:
        parts = m.split(".")
        l1 = parts[0]
        l2 = parts[1] if len(parts) > 1 else "(root)"
        key = (l1, l2)
        if key not in lib2_stats:
            lib2_stats[key] = {
                "top_lib": l1,
                "sub_lib": l2,
                "mods": 0,
                "lines": 0,
                "no_direct_ml_mods": 0,
                "no_direct_ml_lines": 0,
                "no_trans_ml_mods": 0,
                "no_trans_ml_lines": 0,
                "max_in_degree": 0,
                "sum_in_degree": 0,
                "leaf_mods": 0,
                "leaf_lines": 0,
            }
        st = lib2_stats[key]
        ln = mod_lines[m]
        st["mods"] += 1
        st["lines"] += ln
        if not mod_mathlib[m]:
            st["no_direct_ml_mods"] += 1
            st["no_direct_ml_lines"] += ln
        if m not in trans_mathlib:
            st["no_trans_ml_mods"] += 1
            st["no_trans_ml_lines"] += ln
        ind = mod_indeg[m]
        if ind > st["max_in_degree"]:
            st["max_in_degree"] = ind
        st["sum_in_degree"] += ind
        if len(adj_fwd.get(m, ())) == 0:
            st["leaf_mods"] += 1
            st["leaf_lines"] += ln

    lib2_list = sorted(lib2_stats.values(), key=lambda x: -x["lines"])

    # Fine-grained 3-level clusters inside foundational libraries (GroundTheory, Lemmata, BuildAid, Formalism, Development.EtaleCohomology, Development.AutomorphicArithmetic.CommutativeAlgebra, Development.ResolutionOfSingularities)
    foundational_l3 = con.execute(
        """
        SELECT split_part(m.module,'.',1) AS l1,
               split_part(m.module,'.',2) AS l2,
               split_part(m.module,'.',3) AS l3,
               COUNT(*) AS mods,
               SUM(m.lines) AS lines,
               SUM(CASE WHEN NOT m.has_mathlib_import THEN 1 ELSE 0 END) AS no_ml_mods,
               SUM(CASE WHEN NOT m.has_mathlib_import THEN m.lines ELSE 0 END) AS no_ml_lines,
               SUM(CASE WHEN r.local_out_degree = 0 THEN 1 ELSE 0 END) AS leaf_mods,
               SUM(CASE WHEN r.local_out_degree = 0 THEN m.lines ELSE 0 END) AS leaf_lines,
               MAX(r.in_degree) AS max_indeg
        FROM modules m JOIN reachability r USING (module)
        WHERE r.reachable AND (
            m.top_lib IN ('GroundTheory', 'Lemmata', 'BuildAid', 'Formalism', 'PositivityTheory', 'ReciprocityTheory', 'CompanionTheory')
            OR m.module LIKE 'Development.EtaleCohomology.%'
            OR m.module LIKE 'Development.AutomorphicArithmetic.CommutativeAlgebra.%'
            OR m.module LIKE 'Development.ResolutionOfSingularities.%'
        )
        GROUP BY 1, 2, 3
        ORDER BY lines DESC
        LIMIT 60
        """
    ).fetchall()

    # Purely Mathlib-free (no transitive Mathlib import) modules list/breakdown
    pure_noml_by_lib = Counter()
    pure_noml_lines_by_lib = Counter()
    for m in pure_no_trans_mathlib:
        l12 = ".".join(m.split(".")[:2])
        pure_noml_by_lib[l12] += 1
        pure_noml_lines_by_lib[l12] += mod_lines[m]

    # Leaf modules (local_out_degree == 0) breakdown
    leaf_by_lib = con.execute(
        """
        SELECT m.top_lib, split_part(m.module,'.',2) AS l2,
               COUNT(*) AS leaf_mods, SUM(m.lines) AS leaf_lines,
               SUM(CASE WHEN NOT m.has_mathlib_import THEN 1 ELSE 0 END) AS leaf_no_ml_mods,
               SUM(CASE WHEN NOT m.has_mathlib_import THEN m.lines ELSE 0 END) AS leaf_no_ml_lines
        FROM modules m JOIN reachability r USING (module)
        WHERE r.reachable AND r.local_out_degree = 0
        GROUP BY 1, 2
        ORDER BY leaf_lines DESC
        LIMIT 30
        """
    ).fetchall()

    # --- 1(d) Behrend / Iwasawa / Tower / Vandiver Subtree Measurement ---
    def get_keyword_sets(kw: str) -> tuple[set[str], set[str], int]:
        m_rows = con.execute(
            "SELECT m.module FROM modules m JOIN reachability r USING (module) WHERE r.reachable AND lower(m.module) LIKE ?",
            [f"%{kw}%"],
        ).fetchall()
        d_rows = con.execute(
            "SELECT d.module, COUNT(*) FROM decls d JOIN reachability r USING (module) WHERE r.reachable AND (lower(d.name) LIKE ? OR lower(d.signature) LIKE ?) GROUP BY d.module",
            [f"%{kw}%", f"%{kw}%"],
        ).fetchall()
        m_set = {r[0] for r in m_rows}
        d_set = {r[0] for r in d_rows}
        d_cnt = sum(r[1] for r in d_rows)
        return m_set, d_set, d_cnt

    behrend_m, behrend_d, behrend_dcnt = get_keyword_sets("behrend")
    iwasawa_m, iwasawa_d, iwasawa_dcnt = get_keyword_sets("iwasawa")
    tower_m, tower_d, tower_dcnt = get_keyword_sets("tower")
    vandiver_m, vandiver_d, vandiver_dcnt = get_keyword_sets("vandiver")

    # Inspect 4-level breakdown of iwasawa_m to distinguish Iwasawa theory vs Iwasawa decomposition!
    iwasawa_l4 = con.execute(
        """
        SELECT split_part(m.module,'.',1)||'.'||split_part(m.module,'.',2)||'.'||split_part(m.module,'.',3)||'.'||split_part(m.module,'.',4) AS p4,
               COUNT(*) AS mods, SUM(m.lines) AS lines, MIN(r.depth_from_main) AS min_d
        FROM modules m JOIN reachability r USING (module)
        WHERE r.reachable AND lower(m.module) LIKE '%iwasawa%'
        GROUP BY 1
        ORDER BY lines DESC
        LIMIT 30
        """
    ).fetchall()

    # Check specific sub-sets of iwasawa
    iwasawa_avt = {m for m in iwasawa_m if m.startswith("Development.AbelianVarietyTheory.")}
    iwasawa_non_avt = iwasawa_m - iwasawa_avt

    # Also check BehrendSets directory as a whole (in case some files under Formalism.BehrendSets don't have 'behrend' twice - they all have BehrendSets in path!)
    # Compute cones for all sets
    subtrees = {
        "behrend_mod": {
            "decl_match_mods": len(behrend_d),
            "decl_match_count": behrend_dcnt,
            **compute_cones(behrend_m, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        },
        "behrend_mod_or_decl": compute_cones(behrend_m | behrend_d, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        "iwasawa_mod": {
            "decl_match_mods": len(iwasawa_d),
            "decl_match_count": iwasawa_dcnt,
            **compute_cones(iwasawa_m, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        },
        "iwasawa_mod_or_decl": compute_cones(iwasawa_m | iwasawa_d, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        "iwasawa_avt_only": compute_cones(iwasawa_avt, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        "iwasawa_non_avt_only": compute_cones(iwasawa_non_avt, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        "tower_mod": {
            "decl_match_mods": len(tower_d),
            "decl_match_count": tower_dcnt,
            **compute_cones(tower_m, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        },
        "tower_mod_or_decl": compute_cones(tower_m | tower_d, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        "vandiver_mod": {
            "decl_match_mods": len(vandiver_d),
            "decl_match_count": vandiver_dcnt,
            **compute_cones(vandiver_m, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        },
        "behrend_union_iwasawa_mod": compute_cones(behrend_m | iwasawa_m, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        "behrend_union_iwasawa_union_tower_mod": compute_cones(behrend_m | iwasawa_m | tower_m, reach_mods, adj_fwd, adj_rev, mod_lines, mod_depth),
        "iwasawa_l4_breakdown": [
            {"prefix4": r[0], "mods": r[1], "lines": r[2], "min_depth": r[3]} for r in iwasawa_l4
        ],
    }

    # --- Assemble JSON ---
    result = {
        "corpus": {
            "total_modules": len(all_mods),
            "total_lines": total_lines_all,
            "reachable_modules": len(reach_mods),
            "reachable_lines": reach_lines_all,
            "dead_modules": len(dead_mods),
            "dead_lines": dead_lines,
            "dead_pct_lines": round(100.0 * dead_lines / total_lines_all, 3),
            "scan_stats": dict(agg_stats),
            "elapsed_sec": round(time.perf_counter() - t0, 2),
        },
        "explicit_at_bloat": {
            "total_explicit_at_lines": agg_stats["explicit_at_lines"],
            "reach_explicit_at_lines": agg_stats["reach_explicit_at_lines"],
            "pct_of_reach_lines": round(100.0 * agg_stats["reach_explicit_at_lines"] / reach_lines_all, 3),
            "heavy_explicit_files": agg_stats["heavy_explicit_files"],
            "heavy_explicit_total_lines": agg_stats["heavy_explicit_lines"],
            "top25_heavy_at_files": top_heavy_at_files,
        },
        "top30_overall_decls": top30_overall,
        "top30_theorems": top30_theorems,
        "top30_tactic_proof_bodies": top30_tactic_bodies,
        "duplicates": {
            "file_exact": {"summary": file_exact_summary, "top25": top_file_exact},
            "file_norm": {"summary": file_norm_summary, "top25": top_file_norm},
            "decl_norm_span10": {"summary": decl_norm_summary, "top25": top_decl_norm},
            "body_exact_6l": {"summary": body_exact_summary, "top25": top_body_exact},
            "body_norm_6l": {"summary": body_norm_summary, "top25": top_body_norm},
            "tactic_skeleton_12l": {"summary": skel_summary, "top25": top_skel},
            "block6_cross_file": block6_summary,
            "intra_file_dup6": {
                "total_lines": agg_stats["intra_dup_lines_6"],
                "reach_lines": agg_stats["reach_intra_dup_lines_6"],
                "pct_of_reach_lines": round(100.0 * agg_stats["reach_intra_dup_lines_6"] / reach_lines_all, 2),
            },
            "sibling_same_span_top30": [
                {"tail_name": r[0], "span_lines": r[1], "count": r[2], "distinct_mods": r[3], "redundant_lines": r[4], "samples": r[5]}
                for r in sibling_same_span
            ],
            "sibling_numbered_mods_top25": [
                {"pattern": r[0], "count": r[1], "total_lines": r[2], "min_lines": r[3], "max_lines": r[4], "samples": r[5]}
                for r in sibling_mod_families
            ],
            "capelli_upper_b_namespaces_top30": [
                {"ns": r[0], "decls": r[1], "mods": r[2], "sum_span": r[3], "max_span": r[4], "sample_mods": r[5]}
                for r in capelli_prefixes
            ],
        },
        "mathlib_replaceable": {
            "pure_no_transitive_mathlib_mods": len(pure_no_trans_mathlib),
            "pure_no_transitive_mathlib_lines": sum(mod_lines[m] for m in pure_no_trans_mathlib),
            "pure_no_transitive_mathlib_by_lib2": [
                {"lib2": k, "mods": pure_noml_by_lib[k], "lines": pure_noml_lines_by_lib[k]}
                for k, _ in pure_noml_lines_by_lib.most_common(25)
            ],
            "lib2_breakdown_top40": lib2_list[:40],
            "foundational_l3_top60": [
                {
                    "l1": r[0], "l2": r[1], "l3": r[2],
                    "mods": r[3], "lines": r[4],
                    "no_direct_ml_mods": r[5], "no_direct_ml_lines": r[6],
                    "leaf_mods": r[7], "leaf_lines": r[8], "max_indeg": r[9],
                }
                for r in foundational_l3
            ],
            "leaf_modules_top30": [
                {"top_lib": r[0], "sub_lib": r[1], "leaf_mods": r[2], "leaf_lines": r[3], "leaf_no_ml_mods": r[4], "leaf_no_ml_lines": r[5]}
                for r in leaf_by_lib
            ],
        },
        "subtrees": subtrees,
    }

    out_json.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    compression_targets.sort(key=lambda item: (-item["explicit_at_lines"], -item["lines"], item["module"]))
    (out_dir / "heavy82_targets.json").write_text(
        json.dumps(compression_targets, indent=2, ensure_ascii=False), encoding="utf-8"
    )
    con.close()

    print(f"[5/5] Done in {time.perf_counter()-t0:.2f}s -> {out_json}", flush=True)
    print(f"  Reachable: {reach_lines_all:,} lines ({len(reach_mods):,} mods) | Dead: {dead_lines:,} lines ({len(dead_mods):,} mods)")
    print(f"  Explicit-@ lines (reach): {agg_stats['reach_explicit_at_lines']:,} ({result['explicit_at_bloat']['pct_of_reach_lines']}%) in {agg_stats['heavy_explicit_files']} heavy files ({agg_stats['heavy_explicit_lines']:,} lines)")
    print(f"  Whole-file dupes (exact): {file_exact_summary}")
    print(f"  Whole-file dupes (norm):  {file_norm_summary}")
    print(f"  Decl dupes (norm>=10L):   {decl_norm_summary}")
    print(f"  Body dupes (exact>=6L):   {body_exact_summary}")
    print(f"  Body dupes (norm>=6L):    {body_norm_summary}")
    print(f"  Tactic skel dupes(>=12L): {skel_summary}")
    print(f"  Block-6 cross-file red:   {block6_summary['redundant_lines_block6']:,} lines ({block6_summary['pct_of_total_lines']}% of 17.37M)")
    print(f"  Intra-file dup-6 lines:   {agg_stats['reach_intra_dup_lines_6']:,} lines ({result['duplicates']['intra_file_dup6']['pct_of_reach_lines']}%)")
    print(f"  Pure no-trans-Mathlib:    {len(pure_no_trans_mathlib):,} mods, {sum(mod_lines[m] for m in pure_no_trans_mathlib):,} lines")
    print(f"  Behrend cone:             direct={subtrees['behrend_mod']['direct_mods']}({subtrees['behrend_mod']['direct_lines']:,}L), down={subtrees['behrend_mod']['downstream_mods']}({subtrees['behrend_mod']['downstream_lines']:,}L), excl={subtrees['behrend_mod']['exclusive_mods']}({subtrees['behrend_mod']['exclusive_lines']:,}L)")
    print(f"  Iwasawa cone:             direct={subtrees['iwasawa_mod']['direct_mods']}({subtrees['iwasawa_mod']['direct_lines']:,}L), down={subtrees['iwasawa_mod']['downstream_mods']}({subtrees['iwasawa_mod']['downstream_lines']:,}L), excl={subtrees['iwasawa_mod']['exclusive_mods']}({subtrees['iwasawa_mod']['exclusive_lines']:,}L)")
    print(f"  Tower cone:               direct={subtrees['tower_mod']['direct_mods']}({subtrees['tower_mod']['direct_lines']:,}L), down={subtrees['tower_mod']['downstream_mods']}({subtrees['tower_mod']['downstream_lines']:,}L), excl={subtrees['tower_mod']['exclusive_mods']}({subtrees['tower_mod']['exclusive_lines']:,}L)")


if __name__ == "__main__":
    main()
