# Dissecting `grh-lean` (300k Readable) vs. `grh-compact` (76k) vs. Original Alpöge (17.37M Lines)

Generated: 2026-11-26T12:05:44+09:00
Machine-readable backing data: [`reports/grh_vs_compact_summary.json`](grh_vs_compact_summary.json)

## 1. Headline Empirical Comparison

| Metric | Alpöge Original (`v0.2.1`) | `grh/` (300k Readable) | `grh-compact` (76k) | `compact` vs. `readable` |
| --- | ---: | ---: | ---: | ---: |
| `.lean` files | 175,187 | 803 | 794 | -9 |
| Raw lines | 17,374,215 | 477,124 | 112,827 | -76.4% |
| Code lines (no comments/blanks) | 10,737,728 (cone) | 299,902 | 76,149 | -74.6% |
| Unicode source chars | ~980,408,459 | 28,605,259 | 7,036,056 | -75.4% |
| Non-whitespace code chars | — | 13,851,128 | 4,511,672 | -67.4% |
| Normalized Lean tokens | — | 4,836,276 | 1,520,003 | -68.6% |
| Avg non-ws chars / code line | — | 46.19 | 59.25 | **1.28x** packing |
| Median / P95 / Max line length | — | 58 / 92 / 100 | 78 / 97 / 767 | max 767 chars |
| Semicolons (`;`) per 1k code lines | — | 4.79 | 142.16 | **29.68x** |
| Kernel constants / active cone | 804,912 (cone) | 64,358 / 49,821 | 51,804 / 37,569 | -19.5% / -24.6% |
| Kernel export size (MIT `comparator`) | ~61.57 GB | **4.49 GB** (`4,485,867,644 B`) | **5.17 GB** (`5,172,274,528 B`) | **+15.3% larger** |
| Cold build time (MIT same machine) | multi-hour cluster | **32m 12s** | 33m 32s | +80s slower |

## 2. Resolving the Kernel-Export Paradox (-68.6% Source Tokens vs. +15.3% Kernel Export)

Early community discussion treated `grh-compact` primarily as horizontal line-packing code-golf. Full AST/token and tactic-frequency measurement across all 803 + 794 files separates two distinct effects:

1. **Line-packing is only `1.28x` of the `3.94x` line drop**: Code lines drop `299,902 -> 76,149` (`-74.6%`), while average non-whitespace characters per code line rise only `1.28x` (`46.19 -> 59.25`, even as `;` density jumps `29.68x`). The remaining **`3.07x`** is genuine source-token reduction (`-67.4%` non-ws chars, `-68.6%` Lean tokens).
2. **Structural flattening + high-power automation inflate compiled proof terms**:
   - `grh-compact` reorganizes `New.*` from `306` to `219` files (only `74` exact module-path overlaps and `163` basename overlaps), removes **67.5% of `structure` wrappers** (`684 -> 222`), and inlines **61.5% of intermediate `theorem`/`lemma` declarations** (`19,037 -> 7,325`).
   - Explicit tactic steps collapse: `calc` (`2,550 -> 4`, `-99.8%`), `rw` (`14,963 -> 1,121`, `-92.5%`), `exact` (`11,002 -> 974`, `-91.1%`), `refine` (`8,300 -> 920`, `-88.9%`), `have` (`38,151 -> 4,718`, `-87.6%`), `:= by` (`41,328 -> 5,254`, `-87.3%`).
   - Automated closers surge: `tauto` (`78 -> 684`, `8.77x`), `simp_all` (`489 -> 2,042`, `4.18x`), `aesop` (`393 -> 1,258`, `3.20x`), `<;>` (`1,148 -> 3,187`, `2.78x`), `grind` (`1,792 -> 2,713`, `1.51x`).
   - Losing DAG sharing across 11,712 inlined lemmas while generating heavier automation proof terms explains why `grh-compact`'s compiled Lean kernel export is **+686 MB (+15.3%) larger** and compiles **80 seconds slower** than `grh/` readable.

## 3. Top Matched Modules Where `grh-compact` Achieves Genuine Token Compression

Among the 74 exact module-path matches, **64 modules** achieve >=25% non-ws and >=20% Lean-token reduction (`>=2,000` chars saved) — prime candidates for readable, non-packed refactoring on `leanprover-community/riemann-hypothesis:main`:

| Module | `grh/` non-ws | `compact` non-ws | Non-ws delta | Token delta | Packing ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Lib.Shimura.ThetaModuli.FamilyFromPoints` | 39,192 | 10,477 | -28,715 (-73.27%) | -10,456 (-70.06%) | 1.2x |
| `Lib.Cohomology.Hodge.FixedPointFormula` | 32,804 | 5,536 | -27,268 (-83.12%) | -9,394 (-81.55%) | 1.29x |
| `Lib.Cohomology.Etale.ProperFunctors` | 28,987 | 3,188 | -25,799 (-89.0%) | -8,631 (-87.78%) | 1.37x |
| `Lib.ClassField.GreenbergWiles.SplitPrimeReciprocity` | 31,977 | 6,727 | -25,250 (-78.96%) | -8,305 (-75.72%) | 1.33x |
| `Lib.Weil.Construction.FiniteMultiplier` | 29,372 | 6,755 | -22,617 (-77.0%) | -8,017 (-79.85%) | 1.25x |
| `Lib.Cohomology.Hodge.GrothendieckSymbol` | 30,348 | 8,097 | -22,251 (-73.32%) | -7,130 (-71.58%) | 1.4x |
| `Lib.Shimura.ThetaModuli.FlatClosure` | 29,343 | 7,095 | -22,248 (-75.82%) | -8,714 (-76.3%) | 1.37x |
| `Lib.PadicHodge.PeriodRings.Ainf` | 28,003 | 5,861 | -22,142 (-79.07%) | -6,852 (-79.66%) | 1.25x |
| `Lib.GaloisRep.Main.SeedRepresentation` | 30,320 | 8,759 | -21,561 (-71.11%) | -8,028 (-70.99%) | 1.23x |
| `Lib.LocalGL.Iwahori.SortedExponents` | 28,247 | 6,911 | -21,336 (-75.53%) | -8,548 (-76.3%) | 1.25x |
| `Lib.GLn.SchurModule.MinorBasis` | 23,701 | 2,596 | -21,105 (-89.05%) | -8,429 (-91.1%) | 1.44x |
| `Lib.Weil.Construction.WeilOperators` | 24,250 | 3,152 | -21,098 (-87.0%) | -7,796 (-88.86%) | 1.3x |
| `Lib.Shimura.Uniformisation.BallModel` | 29,646 | 8,761 | -20,885 (-70.45%) | -7,099 (-67.71%) | 1.26x |
| `Lib.SiegelWeil.Tower.LargeSideConstantTerm` | 28,055 | 8,072 | -19,983 (-71.23%) | -7,572 (-71.54%) | 1.35x |
| `Lib.Shimura.Deformation.TangentBound` | 26,133 | 6,286 | -19,847 (-75.95%) | -6,418 (-74.8%) | 1.34x |
| `Lib.ClassField.LocalDuality.CrystallineDuality` | 25,679 | 6,184 | -19,495 (-75.92%) | -7,329 (-77.31%) | 1.19x |
| `Lib.Weil.Periods.BesselIntegral` | 24,811 | 5,695 | -19,116 (-77.05%) | -6,616 (-78.02%) | 1.36x |
| `Lib.GLn.SchurModule.SchurMatrix` | 25,936 | 7,024 | -18,912 (-72.92%) | -7,741 (-76.13%) | 1.43x |
| `Lib.General.Geometry.EtaleCharts` | 26,908 | 8,136 | -18,772 (-69.76%) | -6,389 (-68.11%) | 1.43x |
| `Lib.DiscreteSeries.Bruhat.FloorGroups` | 26,518 | 7,767 | -18,751 (-70.71%) | -5,434 (-66.82%) | 1.34x |

## 4. Takeaways for Community Maintenance (`main` on Lean `v4.37.0-rc1` + `TauCeti`)

- **Do not adopt `grh-compact`'s semicolon packing or automation-closer spam**, which expands kernel export size (`+15.3%`) and slows compilation.
- **Do harvest structural flattening** (`in_degree = 1` wrapper/lemma unrolling + Mathlib/`TauCeti` offloading): on `main@e063a92`, `149,521` code lines (**50.0%** of the codebase) belong to single-caller declarations (`single_caller_cross_mod`: 34,598 L; `single_caller_local`: 114,923 L), concentrated in `New.Spanning` (63.0%), `New.Congruences` (70.3%), `New.UpperBound` (60.1%), `New.Determinant` (65.9%), and `New.OneLift` (67.8%).

---

## 한국어 요약

원본 Alpöge(1,737만 줄), `grh/`(30만 줄 readable), `grh-compact`(7.6만 줄) 세 판본을 전체 소스 토큰·택틱 빈도·커널 DB 기준으로 정량 비교한 결과, `grh-compact`의 줄 수 3.94배 감소는 가로 패킹(1.28배)과 실질적인 증명 단축·구조 평탄화(3.07배, 비공백 문자 -67.4%, Lean 토큰 -68.6%)가 결합된 결과임을 확인했습니다. 동시에 명시적 `have`/`rw`/`calc` 단계와 11,712개의 중간 보조정리를 제거하고 `tauto`(8.77배)·`simp_all`(4.18배)·`aesop`(3.20배)·`grind`(1.51배) 등 자동화 택틱으로 대체하면서 커널 DAG 공유가 줄어 실제 커널 export 크기는 오히려 4.49 GB에서 5.17 GB로 15.3% 커지고 콜드 빌드도 80초 느려졌습니다. 따라서 공식 `main` 및 `grh-clean` 트랙에서는 세미콜론 패킹과 자동화 택틱 남발은 배제하고, 구조체 평탄화와 단일 호출 선언(전체의 50.0%, 149,521 코드 줄) 정리, 그리고 64개 공통 모듈에서 확인된 진짜 증명 단축 패턴만 가독성 스타일로 선별 이식하는 것이 최적입니다.
