# Track C — Task 2: Unification Blueprint for the `UnitaryGroupMassFormula` 3-Way Directory Clones

> **Language**: English ([한국어 원문](ko/unitary_dedup_plan.md))

> **Profiler Script**: [profile_unitary_clones.py](../scripts/profile_unitary_clones.py) → raw data [unitary_clone_profile.json](../out/unitary_clone_profile.json)  
> **Representative 3-Way Triplet Unification PoC (Mathlib Drop-In)**: [UnifiedSWeqOm.lean](../poc/UnifiedSWeqOm.lean) (`SWeqOm.lean` × 3 → single parameterized module)  
> **Pure Lean 4.34.1 Core Verification Harness**: [verify_unitary_unified_core.lean](../harnesses/verify_unitary_unified_core.lean) (**`exit 0`, 0 errors, 0 warnings, 0 `sorry`, 0 `axiom`**)

---

## 1. Exhaustive Quantitative Inventory of the 3 Target Directories

Querying `lean_index.duckdb` shows that the 3 subdirectories under `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.*` span **448 modules / 57,658 lines / 2,812,506 bytes**, with **143 filenames appearing across all three directories (triplets)**.

| Directory (`Formalism.PeriodIntegrals.UnitaryGroupMassFormula.*`) | Primary Namespace | Total Modules | Total Lines | Total Bytes | 3-Way Shared (Triplets) | 2-Way Shared (Pairs) | Unique Files | External Import Edges |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **1. `StabilizerOrbitVolume`** | `PI.VolStabSW` (129 modules) | 147 | 19,387L | 944,694B | 143 (18,799L) | 1 (`HformSmulRight`) | 3 (`FibInfEx`, `LocDensHG`, `TopoAFTop`) | — |
| **2. `StabilizerVolume`** | `PI.VolStabS` (133 modules) | 155 | 19,855L | 969,952B | 143 (18,766L) | 2 (`HformSmulRight`, `AdmCpt`) | 10 (`VolStabFromSWS`, `SiegelWeilNarrowOfWide`, `InVolumesAtOfSWS`, `ExStabNu`, etc.) | — |
| **3. `WeilStabilizerVolume`** | `PI.VolStabW` (129 modules) | 146 | 18,416L | 897,860B | 143 (18,028L) | 1 (`AdmCpt`) | 2 (`VolStabFromSWW`, `HformSmulLeft`) | 31 edges |
| **Total** | 3 parallel namespaces | **448** | **57,658L** | **2,812,506B** | **429 files (55,593L)** | **4 files** | **15 files (2,065L)** | Distributed external consumers |

---

## 2. Exhaustive Similarity Distribution & Pairwise Cloning Structure Across the 143 Triplets

Looking only at 3-way minimum normalized similarity (`norm_min`) makes 40 triplets appear `divergent (<50%)`. However, decomposing into the **3 pairs `(Orbit–Stab, Orbit–Weil, Stab–Weil)`** and cross-checking declaration-name sets in DuckDB reveals a far more decisive structure:

### 2.1 Three-Way Similarity Buckets After Normalization (Directory & Namespace Substitution)

| Bucket (3-Way Minimum Normalized Similarity `norm_min`) | Triplets | 3-Copy Total Lines | Redundant Lines if Unified (`sum - max`) | Representative Examples (`[Orbit / Stab / Weil]` lines) |
| :--- | ---: | ---: | ---: | :--- |
| **`exact_100pct` (All 3 copies 100.0% identical)** | **61** | 16,024L | **10,682L** | `ExStabSt` [186/186/186], `FinTheta`, `Unimod`, `Witt`, etc. |
| **`near_identical_95_99` (95% ~ 99.9%)** | **11** | 6,220L | **4,130L** | `SdDual` [510/510/498], `SdTestInf` [344/344/344], `LocDensCnt` [342/354/342], `ExistsUnifFv` [219/214/214], `DensAAOf` [90/90/90] |
| **`high_similar_80_95` (80% ~ 95%)** | **14** | 4,892L | **3,201L** | `LocDensVolS` [345/363/331], `PosNear` [247/267/247], `DensInfCo` [189/180/180], `TopoNuFin` [164/174/164], `UnifVSpec` [137/137/137], `SWeqOm` [71/74/71], `VolStabFromSWOf` [47/47/47] |
| **`moderate_50_80` (50% ~ 80%)** | **17** | 9,914L | **6,453L** | `SdUniq` [404/429/393], `TensTop` [244/246/255], `DensVNA` [175/145/141], `ESSymmApply` [166/175/164] |
| **`divergent_lt50` (< 50%)** | **40** | 18,543L | **11,624L** | `LocDensHF` [401/408/408], `LocDensHH` [396/379/396], `DensGen` [286/263/256], `LocDensCntQ` [125/147/125] |
| **Total** | **143** | **55,593L** | **36,090L** | — |

### 2.2 Pairwise 100% Identity & Declaration-Name Set Cross-Check (Key Structural Discovery)

| Pairwise / Declaration-Match Category | Triplets | Share (of 143) | Structural Cause |
| :--- | ---: | ---: | :--- |
| **All 3 copies 100.0% identical after normalization** (`all3 == 1.0`) | **61** | **42.7%** | Pure shared lemmas independent of all 3 parameter axes (58/143 are exact verbatim raw-text matches) |
| **2 of 3 copies 100.0% identical** (`2-of-3 == 1.0`) | **54** | **37.8%** | Clean 2:1 clustering driven by the 3 parameter axes below: |
| ├─ `Orbit == Weil == 1.0` (only `Stab` differs) | 32 | 22.4% | `Orbit` and `Weil` share non-smooth `IsAdm`, while only `Stab` uses `IsAdmS` (`IsSmoothCc`) |
| ├─ `Stab == Weil == 1.0` (only `Orbit` differs) | 18 | 12.6% | `Stab` and `Weil` share the dimension bound `2 * a < M`, while only `Orbit` uses `a + 2 ≤ M` |
| └─ `Orbit == Stab == 1.0` (only `Weil` differs) | 4 | 2.8% | `Weil`-specific `SWc1W` dependency path (`SdDual`, `DensVSt`, etc.) |
| **All 3 copies ≥ 90% similar (tiny diff)** | **7** | **4.9%** | 2-line difference in `InCtx` signature (`DensAAOf`, `UnifVSpec`, `VolStabFromSWOf`, `ExChar`, etc.) |
| **2 copies ≥ 90% similar** | **2** | **1.4%** | Partial refactoring differences |
| **All 3 copies < 90% (independently generated tactics)** | **19** | **13.3%** | Direct diff inspection of `DensGen`, `LocDensHH`, and `LocDensCntQ` confirms many are **independent re-proofs of identical mathematical theorem signatures in different tactic styles** (`have h` vs. `have h0`, `calc` vs. `unfold`) |
| **100% identical declaration-name sets across all 3 (DuckDB cross-check)** | **115 / 143** | **80.4%** | The remaining 28/143 also have partial overlaps — the entire directory tree is effectively a 3-copy clone of the same DAG |

---

## 3. Exact Mathematical & Type-Parameter Axes Separating the 3 Directories (Diff-Verified)

Direct diff inspection of the representative context modules (`StabilizerOrbitVolume/FibInfEx.lean`, `StabilizerVolume/VolStabFromSWS.lean`, `WeilStabilizerVolume/VolStabFromSWW.lean`) together with `SWeqOm.lean`, `PosTest.lean`, `ExChar.lean`, `DensAAOf.lean`, `UnifVSpec.lean`, and `VolStabFromSWOf.lean` establishes that **every difference across the 3 directories reduces to exactly 3 Orthogonal Parameter Axes**:

| Parameter Axis (`VolStabCfg` Field) | 1. `StabilizerOrbitVolume` (`PI.VolStabSW`) | 2. `StabilizerVolume` (`PI.VolStabS`) | 3. `WeilStabilizerVolume` (`PI.VolStabW`) | Source Diff Evidence |
| :--- | :--- | :--- | :--- | :--- |
| **Axis 1: Dimension Stability Condition (`dimBound a M`)** | `a + 2 ≤ M` | **`2 * a < M`** | **`2 * a < M`** | `FibInfEx.lean:16` vs. `VolStabFromSWS.lean:19` vs. `VolStabFromSWW.lean:47`; `ExChar.lean:15` (`0 + 2 ≤ M` vs. `2 * 0 < M`); `DensAAOf.lean:81` (`ha2` vs. `by omega`, since `1 ≤ a → 2*a < M → a + 2 ≤ M`) |
| **Axis 2: Archimedean Test-Function Regularity (`archExtra Φinf`)** | `True` (`IsAdm`: `Continuous ∧ HasCompactSupport`) | **`IsSmoothCc F E Φinf`** (`IsAdmS`: `IsAdm ∧ IsSmoothCc`, forgetful map `IsAdmS.adm`) | `True` (`IsAdm`: `Continuous ∧ HasCompactSupport`) | `VolStabFromSWS.lean:39-50`, `SWeqOm.lean:47-49` (`hsm` added), `PosTest.lean:36` (`hadm.adm`), `ExChar.lean:27` (`isSmoothCc_empty`), `VolStabFromSWOf.lean:32` |
| **Axis 3: Analytic Siegel–Weil Input Hypothesis (`swInput F E σ M J`)** | **`SWc1 F E σ M J`** (Siegel–Weil in range `a + 2 ≤ M`) | **`StabilizerFirstChernCompatibility F E σ M J`** (Siegel–Weil restricted to `2 * a < M`, `IsSmoothCc`, via `SiegelWeilNarrowOfWide`) | **`SWc1W F E σ M J`** (`RapidDecay` Siegel–Weil in range `2 * a < M`) | `FibInfEx.lean:16`, `VolStabFromSWS.lean:19`, `VolStabFromSWW.lean:16-38, 47`; all three hypotheses feed into the identical adelic theta-average Euler product identity (`sw_eval`) |

### Monotonic Hierarchy (Core Mathematical Insight)
- Whenever `1 ≤ a`, **`2 * a < M → a + 2 ≤ M`** always holds (1-line `omega` proof; equivalent to `3 ≤ M` when `a = 1`, and `2a + 1 ≥ a + 2` when `a ≥ 2`).
- Consequently, the hypotheses weaken monotonically along **`SWc1 → SWc1W → StabilizerFirstChernCompatibility`** (equivalently, tightening the required input class / adjusting domain scope), and the three directories are literally **3 full copy-pasted instantiations of the exact same adelic orbital-integral, local-density, and Siegel–Weil decomposition proof pipeline** specialized to `cfgOrbit`, `cfgStab`, and `cfgWeil`.

---

## 4. Single Parameterized Unification Architecture & Quantitative Savings Estimate

### 4.1 Proposed Module Architecture (`Formalism.PeriodIntegrals.UnitaryGroupMassFormula.Common.*`)
1. **`Common.Config`** (~140L, defined once): defines `structure VolStabCfg`, `InCtx cfg`, `IsAdmCfg cfg`, `IsAdmCfg.toBase`, `DensFibInf cfg`, `DensFibV cfg`, `SWeqOm cfg`, `Unfold cfg`, `PosTest cfg`, and the 3 concrete instances `cfgOrbit`, `cfgStab`, `cfgWeil`.
2. **`Common.PureShared.*`** (61 `exact_100pct` triplets): defined once without parameterization (`ExStabSt`, `FinTheta`, `Unimod`, `Witt`, `TopoGram`, `RestrProdG`, etc.), with thin `abbrev`/re-export shims or direct import substitution in the 3 directories.
3. **`Common.ParamPipeline.*`** (54 `2-of-3 == 1.0` + 28 variant triplets): unified into single theorems parameterized by `(cfg : VolStabCfg)` (`sWeqOm_of cfg`, `posTest_of cfg`, `exChar_holds cfg`, `volStabFromSW_of cfg`, `densAAOf cfg`, `unifVSpec cfg`, etc.). For the 19 triplets like `DensGen`, `LocDensHH`, and `LocDensCntQ` that prove the same theorem with different tactics, retain the single shortest, cleanest proof.
4. **Thin Compatibility Facades (3 Directory Entrypoints)**: re-expose existing symbols via `abbrev` at each directory's root/entrypoint (`Assembly`, `VolStabFromSWS`, `VolStabFromSWW`) so none of the 31+ external importers (`NcXBoxSteps`, `NcXLocSB`, `DecoratedLatticeProofs.*`, etc.) break.

### 4.2 Static Line-Reduction Estimates (3 Scenarios, Baseline 57,658L Total / 55,593L Triplets)

| Unification Scenario | Target Scope | Estimated Static Line Reduction | Share of 3 Directories (57,658L) | Notes |
| :--- | :--- | ---: | ---: | :--- |
| **Conservative Lower Bound (Mechanical 100% Clones Only)** | 61 3-way 100% triplets (drop 2 copies: 10,682L) + 54 2-way 100% triplets (drop 1 copy: 8,386L) | **-19,068L** | **-33.1%** | 0% proof-logic changes; pure duplicate elimination only |
| **Recommended Parameterized Unification (`VolStabCfg`, Similarity ≥ 80%)** | Unify 61 + 54 + high/near-identical triplets (net of 10–15L/file adapter overhead) | **-30,224L** | **-52.4%** | 3-axis `VolStabCfg` unification + thin 1-line instantiations |
| **Full Unification Upper Bound (All 143 Triplets Unified)** | Unify down to 1 shortest proof across all 115/143 identical declaration sets and all 19 tactic-style-divergent triplets | **-36,090L** *(~35,500L net of ~500L adapters)* | **-62.6%** *(~61.6% net)* | All 15 directory-unique files (2,065L) remain intact |

---

## 5. Representative Triplet Unification PoC Results (`SWeqOm.lean` × 3 → Single Unified Module)

### 5.1 Static Refactoring Metrics ([UnifiedSWeqOm.lean](../poc/UnifiedSWeqOm.lean))
- **Selected Triplet**: `SWeqOm.lean` — the canonical triplet that **exercises all 3 axes simultaneously** (`dimBound`, `archExtra`/`IsSmoothCc`, and `swInput`/`SWc1`·`StabilizerFirstChernCompatibility`·`SWc1W`).
  - Original 3 files: `StabilizerOrbitVolume/SWeqOm.lean` (71L) + `StabilizerVolume/SWeqOm.lean` (74L) + `WeilStabilizerVolume/SWeqOm.lean` (71L) = **216L** (of which `Decay` 33L × 3 = 99L is verbatim copy-paste).
  - Unified `SWeqOm` core (`Decay` + unified `sWeqOm_of` + instantiation wrappers): **73L** (**-143L, -66.2%**).
  - Entire self-contained PoC file (`UnifiedSWeqOm.lean`, including the one-time definitions shared by all 143 triplets — `VolStabCfg`, `InCtx`, `IsAdmCfg`, `DensFib*`, `SWeqOm`, and the 3 `cfg*` instances): **251L (187L code)** — reducing the 3 `SWeqOm.lean` files (216L) + 3 context files (`FibInfEx` 123L + `VolStabFromSWS` 148L + `VolStabFromSWW` 163L = 434L) from **650L → 251L (-399L, -61.4%)**.
  - 0 `sorry`, 0 `axiom`, 0 `admit` in code.

### 5.2 Standalone Lean 4.34.1 Core Harness Compilation Verification
- **File**: [verify_unitary_unified_core.lean](../harnesses/verify_unitary_unified_core.lean) (221L, 0 Mathlib imports)
- **Command**: `elan run leanprover/lean4:v4.34.1 lean ../harnesses/verify_unitary_unified_core.lean`
- **Result**: **`exit code 0` (0 errors, 0 warnings, 0 `sorry`, 0 `axiom`)**
- **Mechanically Verified Items**:
  1. `two_mul_lt_implies_add_two_le : 1 ≤ a → 2 * a < M → a + 2 ≤ M` (`omega`)
  2. `IsAdmCfg.toBase` (generalizing `IsAdmS.adm` uniformly across all configurations)
  3. Proof of the single unified theorem `sWeqOm_of (cfg : VolStabCfg C)` and recovery of all 3 directory-specific instances (`PI_VolStabSW_sWeqOm_of`, `PI_VolStabS_sWeqOm_of`, `PI_VolStabW_sWeqOm_of`)
  4. Formal proofs of the monotonic hierarchy theorems `swc1_implies_swc1W` and `swc1W_implies_swFirstChern`
