# Riemann Hypothesis Lean Dissection

Static analysis, standalone Lean harnesses, and refactoring experiments for Levent Alpöge's published Lean 4 formalization of the Riemann Hypothesis and of Dirichlet L-functions.

- [Original release announcement](https://alpo.ge/remark.pdf) and [source mirror](https://github.com/leanprover-community/riemann-hypothesis).
- **[Standalone Kernel-Grounded Minimal Backbone Spec](https://github.com/thekeunpie-hash/rh-kernel-backbone)** ([interactive web edition](https://thekeunpie-hash.github.io/rh-kernel-backbone/)).
- Upstream simplification PRs verified on Lean `v4.33.1` (both **merged**): [PR #60](https://github.com/leanprover-community/riemann-hypothesis/pull/60) (`173225e84`, `FixPiIff.lean`, `8,029 → 45` L) and [PR #65](https://github.com/leanprover-community/riemann-hypothesis/pull/65) (`f1f6d6542`, 4 kernel-used `CapelliIdentities` files, `5,073 → 591` L, `105 → 0` warnings).
- [Andrew Sutherland's independent verification at MIT](https://math.mit.edu/~drew/grh/).
- [Haejoe's walkthrough of the 17-million-line source tree](https://haejoe.com/en/column/riemann-hypothesis-lean-17m-lines-dissection) ([한국어](https://haejoe.com/column/riemann-hypothesis-lean-17m-lines-dissection)).

## Verification scope

The local audit scanned the upstream source tree, indexed imports and declarations, and traced dependencies from `Main`. Its token and dependency counts are static evidence. The seven files in `harnesses/` compile independently against Lean v4.34.1 and exercise representative proof transformations in simplified models. The two Mathlib-dependent files in `poc/` are proposed refactorings. Their corresponding harnesses validate the modeled transformations, while integrating the PoCs into the upstream project requires the upstream toolchain and dependencies.

Sutherland's independent verification covers the complete upstream build on Lean and Mathlib v4.33.1. His [axiom audit](https://math.mit.edu/~drew/grh/audit.log) reports that the five headline theorems depend on `propext`, `Classical.choice`, and `Quot.sound`. His verification page documents the build, kernel checks, and provenance.

## Reproduce the standalone checks

Install [Elan](https://github.com/leanprover/elan), then run from this repository root. The harnesses require the Lean toolchain only.

```sh
elan toolchain install leanprover/lean4:v4.34.1
for file in harnesses/*.lean; do
  elan run leanprover/lean4:v4.34.1 lean "$file" || exit
done
```

With Python installed, `python scripts/verify_round2.py --harnesses harnesses` runs the same checks on Windows, macOS, and Linux and also scans for forbidden tokens such as `sorry` and `axiom` in the harness code.

## Reproduce the static analysis

Use Python 3.10 or later and install DuckDB. Extract the original release into `lean/` so that `lean/src/Main.lean` exists. For provenance and archive checksums, use the [MIT verification page](https://math.mit.edu/~drew/grh/#provenance).

```sh
python -m pip install duckdb
python scripts/index_lean.py
python scripts/deep_audit.py
python scripts/analyze_bloat.py
python scripts/profile_unitary_clones.py
python scripts/de_explicit_capelli.py
python scripts/verify_round2.py --capelli-shadow out/capelli_shadow
python scripts/verify_round2.py --check-golf poc/golfed_RingObjectsOfMatrixData.lean
```

The index defaults to `out/lean_index.duckdb`. The bloat scan generates `out/heavy82_targets.json`, which feeds the Capelli rewrite. The rewrite writes a separate shadow tree. To generate an isolated stub, pass `--module`, `--decl`, and optionally `--out` to `scripts/make_stub.py`. To check citations against the local source and index, pass the report paths to `scripts/verify_round2.py --refs`. See each script's `--help` for supported flags.

Path options `--src-root`, `--index-db` where the script uses DuckDB, and `--out-dir` override `LEAN_SRC_ROOT`, `LEAN_INDEX_DB`, and `OUT_DIR`, respectively. The defaults are relative to this repository. The indexer requires a fresh database path when rebuilding. Report references under `../lean/` point to the separately extracted source. References under `../out/` describe generated or historical run artifacts. The release source, DuckDB database, TSV intermediates, and compiled files are excluded from this repository.

Start with the **[Kernel-Grounded Minimal Backbone Specification](reports/minimal_backbone_spec.md)** (backed by the machine-readable [kernel_backbone_summary.json](reports/kernel_backbone_summary.json) and verified to 0 dead citations with [`scripts/audit_spec_citations.py`](scripts/audit_spec_citations.py)), the [audit verdict](reports/meta_audit_verdict.md), the [proof walkthrough](reports/rh_proof_explained.md), and the [Round 2 review](reports/critic_signoff.md). The [Rosetta Stone](reports/rosetta_stone.md) maps Alpöge's nine announcement claims to kernel-active source declarations (`in_cone = true`), and the [Capelli batch](reports/capelli_batch_report.md), [unitary deduplication](reports/unitary_dedup_plan.md), and [tactic golf](reports/tactic_golf_report.md) reports record the compression experiments. All reports in `reports/` are written in English; the original Korean editions are archived under [`reports/ko/`](reports/ko/).

## 한국어 요약

Levent Alpöge가 공개한 리만 가설과 디리클레 L-함수 일반화 리만 가설의 Lean 4 코드를 정적으로 분석한 자료입니다. `scripts/`에는 전체 소스의 선언과 의존성을 조사하는 도구가 있고, `harnesses/`의 7개 파일은 Lean v4.34.1에서 대표 변환을 독립적으로 검증합니다. 전체 소스 빌드와 표준 3공리 확인은 [MIT Andrew Sutherland의 독립 검증](https://math.mit.edu/~drew/grh/)에 기록되어 있습니다. 상세 리포트 한국어 원문은 [`reports/ko/`](reports/ko/)에 보관되어 있으며, 분석 개요는 [해줘닷컴 칼럼](https://haejoe.com/column/riemann-hypothesis-lean-17m-lines-dissection)에서 읽을 수 있습니다.

The analysis and compression scripts and independent harnesses are available under the [MIT License](LICENSE). The original RH/GRH formalization is Alpöge's separate release.
