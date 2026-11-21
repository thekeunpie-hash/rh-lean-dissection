# De-elaboration of the 82 heavy `pp.explicit` files

> **Language**: English ([한국어 원문](ko/capelli_batch_report.md))

> **Execution Engine**: [de_explicit_capelli.py](../scripts/de_explicit_capelli.py) (v2, runtime `44.76s`)  
> **Target Input List**: [heavy82_targets.json](../out/heavy82_targets.json) (**100% exact match, 0-line discrepancy** with Round 1 [bloat_analysis_data.json](../out/bloat_analysis_data.json) `heavy_explicit_files = 82`, `heavy_explicit_total_lines = 75,221L`)  
> **Raw Verification Manifest**: [capelli_batch_manifest.json](../out/capelli_batch_manifest.json)  
> **Transformed Shadow Tree**: `../out/capelli_shadow/` (original `downloads/lean/src/` **0 bytes changed**)

---

## 0. Static savings and harness compiles are different measurements

Only `leanprover/lean4:v4.34.1` is installed locally; neither the repository's `leanprover/lean4:v4.33.1` toolchain nor prebuilt Mathlib `rev 0df444a3` `.olean` caches (`downloads/lean/.lake/`) are present. Accordingly, the two metric classes below are reported strictly separately.

| Verification Category | Scope | Before | After | Reduction (% Saved) | Verification Method & Status |
| :--- | :--- | ---: | ---: | ---: | :--- |
| **Static Transformation Savings (All 82 Files)** | All 82 files in Round 1 `heavy_explicit_files` | **75,221L** (5,825,527B) | **13,612L** (1,008,203B) | **-61,609L (-81.90%)** / **-4,817,324B (-82.69%)** | AST parser + 100% declaration-name preservation (1,542/1,542) + delimiter balance 82/82 + **0** notation instance leaks + phantom implicit named preservation (**116** sites) + 0 `sorry`/`axiom`/`admit` + 0 safety rollbacks |
| ├─ **Static Transformation Savings (`CapelliIdentities` 46 files)** | 46 files under `CapelliIdentities` out of the 82 | **66,974L** (5,266,582B) | **6,119L** (498,725B) | **-60,855L (-90.86%)** / **-4,767,857B (-90.53%)** | Accounts for **98.78%** of total line savings (`@`-lines `55,875 → 703`, -98.74%) |
| ├─ **Static Transformation Savings (Actual `pp.explicit` 51 files)** | 46 `CapelliIdentities` + 5 `Lemmata.*` files | **68,146L** (5,339,610B) | **6,537L** (522,286B) | **-61,609L (-90.41%)** / **-4,817,324B (-90.22%)** | Conversion of all `pp.explicit` serialized dumps (`361` declarations rewritten) |
| └─ **Preserved Manual-`@` Files (31 files, False-Positive Guard)** | 31 files using ordinary hand-written `@` tactics rather than `pp.explicit` | **7,075L** (485,917B) | **7,075L** (485,917B) | **0L (0.00%)** | **Intentionally untouched** — **0%** corruption rate on manual `@lemma` tactic calls |
| **Standalone Lean 4.34.1 Core Harness Compilation Verification** | **5 structurally distinct representative modules/theorem families** (`FixPiIff`, `CovariantDegrees`, `MemOfClosed`, `MulMemIntA`, unified `Re3`/`Re4`) | 5 representative originals total **28,572L** (**733L** after shadow transform, -97.43%; 6 files including twin `Re3`: **32,241L → 961L**) | 5 pure Lean 4 core harnesses (**907L** total, including kernel `rfl` definitional-equality proofs between explicit `@` and de-elaborated forms) | **5 / 5 compiled** | `elan run leanprover/lean4:v4.34.1 lean <file>` **all `exit 0`, 0 errors, 0 warnings, 0 `sorry`, 0 `axiom`** |

### Correction to the Round 1 framing
Round 1 [bloat_report.md](../out/bloat_report.md#L144) loosely referred to `heavy_explicit_files = 82 (75,221L)` (criterion: `reachable ∧ explicit_at_lines ≥ 20 ∧ explicit_at_lines / code_lines ≥ 0.15`) as "82 heavy `Capelli` files". Tracing the 82 paths gives the exact breakdown:
- **Under `Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.*`**: **46 files / 66,974L / 55,875 `@`-lines** (**89.04%** of total lines across the 82 files, **95.73%** of all `@`-lines, and **98.78%** of all lines saved).
- **External library `pp.explicit` dumps (`Lemmata.*`)**: **5 files / 1,172L / 718 `@`-lines** (`Lemmata.GeneralBFactRightTerForm.Imports`, `GeneralBFactLeftAltForm.MQ`, `GeneralBFactLeftVersion.Imports`, `ClearingDenominators.UmonLeUzmon`, `GeneralBFactThirdVersion.Imports`).
- **External library manual-`@` files**: **31 files / 7,075L / 1,772 `@`-lines** (`MultiplicationLatticeSecond` 924L, etc. — hand-written `@` calls rather than `pp.explicit` dumps). `de_explicit_capelli.py` automatically classifies these 31 files and **preserves them verbatim without changing a single character**.

---

## 1. Two-Tier Safe AST Engine Design (`de_explicit_capelli.py`)

1. **Comment-, String-, Unicode-, and Balanced-Delimiter-Aware Parser**:
   - Accurately tokenizes `--` line comments, nested `/- ... -/` block comments, string literals `"..."`, attributes `@[...]`, as-patterns `x@⟨...⟩`, universe levels `.{u_1, u_2}`, and Greek/subscript Unicode identifiers (`Ω`, `σ`, `τ`, `ε`, `Λ`, `ρ`, `χ₁`, etc.).
   - During top-level declaration segmentation, separates `attribute [local instance]`, `section`, `end`, `namespace`, `open`, and `variable` commands into independent non-declaration blocks, structurally eliminating the bug where trailing commands get swallowed into a preceding `def` body.
   - Tracks quantifier depth (`quant_depth`) for `∀`/`∃` while scanning lambda arguments so expressions like `Set.ofPred (fun a ↦ ∀ v, P v)` never terminate prematurely at the inner `,`, and never strips outer parentheses around type ascriptions `(1 : Complex)` or tuples `(a, b)`.
2. **Tier 1 — Verified Schema-Driven Full De-Elaboration (24,465 applications)**:
   - Applies exact arities and `(explicit)` / `{implicit}` / `[instance]` slot layouts for 118 core Mathlib/Core symbols (`NumberField`, `RingOfIntegers`, `adicCompletion`, `FiniteAdeleRing`, `ValuativeRel`, `Valuation.integer`, `ResidueField`, `Units`, `Subgroup`, `RingHom`, `AlgHom`, `AlgEquiv`, `LinearMap`, `ContinuousLinearMap`, `TensorProduct`, `Representation`, `Matrix.GeneralLinearGroup`, `HasQuotient.Quotient`, `DFunLike.coe`, `OneHom.toFun`, `Membership.mem`, `Eq`, `LE.le`, `HAdd`/`HMul`/`HSMul`/`HPow`, `OfNat.ofNat`, `ite`, etc.).
   - Applies **364 project-local binder schemas** parsed directly from full untruncated source files (avoiding DuckDB's 250-character truncated column), enforcing two guards: (a) a four-way safety check confirming that every argument stripped from an `[instance]` slot is genuinely an instance term (`@*.to*`, `@*inst*`, `inst_k`, `hl`, `hP`), and (b) transitive inferability fixed-point analysis that automatically detects **phantom implicit binders (`{E}`, `{K}`, etc.) uninferable from both explicit parameter types and the return type**, preserving them as named arguments `(E := E)` / `(K := K)` (**116** applications total; anonymous uninferable binders safely fall back to Tier 2).
3. **Tier 2 — Arity-Preserving Wildcard Folding for Unregistered Symbols (9,611 applications, 13,886 instance slots folded)**:
   - For any `@Head arg₀ ... argₖ` absent from the Tier 1 catalog, preserves **`@Head`, universe levels `.{...}`, and every positional argument slot 1:1**, replacing only purely synthesized typeclass dictionaries (`@*.to*`, `@*inst*`, standard Mathlib dictionaries) with `_`. This drives the structural probability of dropping a value or type argument on an unknown declaration to **0%**.
4. **Automated Post-Transform Integrity Verification & v2 Regression Guards (82/82 Files Passed)**:
   - **100% Declaration-Name Preservation**: `1,542 / 1,542` (`theorem`/`lemma`/`def`/`abbrev`/`structure`/`class`/`inductive`/`instance`/`axiom`/`opaque`, 0 dropped, 0 renamed).
   - **Delimiter & Bracket Balance**: `82 / 82` (`()`, `[]`, `{}`, `⟨⟩` all balanced; `0` safety rollbacks).
   - **Notation Instance Leak Check (`check_notation_instance_leaks`)**: check for typeclass instances erroneously emitted on the right-hand side of `→L[...]`, `→ₗ[...]`, or `⧸` → **`0 / 82` files (`0` leaks)**.
   - **Zero Forbidden Tokens Introduced**: `0` new `sorry`, `0` new `axiom`, `0` new `admit`.
   - **v2 Fixes (incorporating review note #32)**:
     - Fixed the `ContinuousLinearMap` 13-argument schema off-by-one: corrected the codomain `M₂` slot from `args[9]` (`[TopologicalSpace M₂]`) to the true `args[8]` (`M₂`), restoring all 24 `→L[Complex]` sites in `HloweqTransfer.lean` and `ComplexNormedInstanceCompat.lean` to `(L2 ε) →L[Complex] (L2 ε)`.
     - Automated named preservation of phantom implicit binders (`phantom_named_preserved = 116`): restored `CovariantDegrees.KwF (E := E)` (36/36 calls in the final shadow), `SelectionLemmas.hcompl (K := K)` and `loc (K := K)` (3 sites), and `SquareOfApproximation.IsSplit (E := E)` (1 site).

---

## 2. Top 25 Files Static Transformation Results (Full 82-File Breakdown in `capelli_batch_manifest.json`)

| Rank | Module (`CapelliIdentities.*` abbreviated `CI.`) | Before L | After L | Saved L (% Cut) | Before B → After B | `@`-Lines (Before→After) | Decls (Rewritten/Total) | Decls / Delims | Risk Tier |
| ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: | :---: | :--- |
| 1 | `CI.FixPiIff` | 8,029 | 37 | **-7,992 (-99.5%)** | 732,359 → 3,451 | 7,969 → 4 | 1 / 2 | OK / OK | **HIGH** (`complRel`, `isLocalField`), MED |
| 2 | `CI.CovariantDegrees` | 6,170 | 248 | **-5,922 (-96.0%)** | 504,790 → 29,009 | 5,776 → 28 | 25 / 29 | OK / OK | **HIGH** (`aux*`), MED (Alg/Val/Normed) |
| 3 | `CI.MemOfClosed` | 5,746 | 155 | **-5,591 (-97.3%)** | 478,050 → 11,139 | 5,313 → 11 | 10 / 12 | OK / OK | **HIGH** (`aux1`/`algRes`), MED (Val) |
| 4 | `CI.MulMemIntA` | 4,969 | 76 | **-4,893 (-98.5%)** | 405,284 → 8,425 | 4,630 → 9 | 8 / 9 | OK / OK | **HIGH** (`aux3`), MED (Val/Alg) |
| 5 | `CI.HloweqTransfer` (`Re4`) | 3,658 | 217 | **-3,441 (-94.1%)** | 282,214 → 26,224 | 3,020 → 45 | 26 / 27 | OK / OK | **HIGH** (`inst*`), MED (Normed/Meas) |
| 6 | `CI.ComplexNormedInstanceCompat` (`Re3`) | 3,669 | 228 | **-3,441 (-93.8%)** | 283,079 → 27,089 | 3,019 → 44 | 26 / 27 | OK / OK | **HIGH** (`inst*`), MED (Normed/Meas) |
| 7 | `CI.SelectionLemmas` | 3,547 | 390 | **-3,157 (-89.0%)** | 252,719 → 31,813 | 2,941 → 33 | 23 / 34 | OK / OK | **HIGH** (`aux*`) |
| 8 | `CI.FreeModuleQuotient` | 2,516 | 91 | **-2,425 (-96.4%)** | 207,153 → 4,392 | 2,293 → 0 | 1 / 2 | OK / OK | MED (Alg/Quotient) |
| 9 | `CI.ZeroContDiffOnSupported` (`H23`) | 2,229 | 208 | **-2,021 (-90.7%)** | 170,621 → 15,306 | 1,915 → 29 | 16 / 20 | OK / OK | **HIGH** (`aux*`), MED (Val/Topo) |
| 10 | `CI.BorelApproximation` | 2,216 | 196 | **-2,020 (-91.2%)** | 172,169 → 15,838 | 1,915 → 29 | 16 / 20 | OK / OK | **HIGH** (`aux*`), MED (Val/Topo) |
| 11 | `CI.RootEquality` | 2,343 | 744 | **-1,599 (-68.2%)** | 159,339 → 42,679 | 1,377 → 24 | 15 / 54 | OK / OK | MED (Val) |
| 12 | `CI.CoboundaryOfGenerator` | 1,701 | 141 | **-1,560 (-91.7%)** | 120,528 → 13,588 | 1,381 → 31 | 9 / 10 | OK / OK | MED (Topo) |
| 13 | `CI.ImportsMoreExtra` | 1,551 | 67 | **-1,484 (-95.7%)** | 132,081 → 6,902 | 1,411 → 13 | 5 / 5 | OK / OK | **HIGH** (`aux*`), MED (Alg) |
| 14 | `CI.IntegerSpanGenerators` | 1,746 | 270 | **-1,476 (-84.5%)** | 162,957 → 26,873 | 893 → 36 | 2 / 11 | OK / OK | LOW (Tier-2 `_`) |
| 15 | `CI.ConjInvariantCharacterMem` | 1,756 | 295 | **-1,461 (-83.2%)** | 127,799 → 24,264 | 1,216 → 28 | 23 / 31 | OK / OK | **HIGH** (`aux*`), MED (Alg) |
| 16 | `CI.ContDiffHerm` | 1,727 | 290 | **-1,437 (-83.2%)** | 100,791 → 20,955 | 1,078 → 60 | 16 / 29 | OK / OK | **HIGH** (`aux*`), MED (Normed) |
| 17 | `CI.BlockHomomorphism` | 1,484 | 106 | **-1,378 (-92.9%)** | 96,581 → 9,953 | 1,061 → 17 | 10 / 12 | OK / OK | LOW (Tier-2 `_`) |
| 18 | `CI.EqZeroOfForallIntegralCoeff` | 1,180 | 318 | **-862 (-73.0%)** | 85,986 → 22,107 | 811 → 14 | 7 / 25 | OK / OK | **HIGH** (`aux*`), MED (Normed/Topo) |
| 19 | `CI.PhiMul` | 834 | 23 | **-811 (-97.2%)** | 74,945 → 2,889 | 757 → 4 | 1 / 1 | OK / OK | MED (Alg) |
| 20 | `CI.PlaceRankTwoOne` | 1,067 | 334 | **-733 (-68.7%)** | 69,413 → 20,986 | 681 → 17 | 14 / 29 | OK / OK | **HIGH** (`aux*`), MED (Normed/Topo) |
| 21 | `CI.InvolutionInvariants` | 821 | 123 | **-698 (-85.0%)** | 56,921 → 10,959 | 649 → 19 | 13 / 15 | OK / OK | **HIGH** (`aux*`), MED (Normed/Topo) |
| 22 | `CI.UnopSMul` | 646 | 30 | **-616 (-95.4%)** | 56,522 → 2,669 | 609 → 5 | 3 / 3 | OK / OK | MED (Alg) |
| 23 | `CI.FiniteCohomologyOfTrivialOfCyclic` | 608 | 45 | **-563 (-92.6%)** | 48,130 → 4,958 | 534 → 7 | 1 / 2 | OK / OK | LOW (Tier-2 `_`) |
| 24 | `CI.FgZ1T` | 523 | 66 | **-457 (-87.4%)** | 41,317 → 6,901 | 442 → 8 | 1 / 1 | OK / OK | MED (Alg) |
| 25 | `CI.HolSubMul` | 482 | 60 | **-422 (-87.5%)** | 38,164 → 4,881 | 247 → 27 | 3 / 4 | OK / OK | LOW (Tier-2 `_`) |
| — | **Remaining 26 Modified Files** (`CI.` 21 + `Lemmata.` 5) | 6,928 | 1,779 | **-5,149 (-74.3%)** | 479,698 → 128,036 | 4,655 → 184 | 86 / 109 | OK / OK | HIGH 2, MED 9 |
| — | **Unmodified Manual-`@` Files (31)** | 7,075 | 7,075 | **0 (0.0%)** | 485,917 → 485,917 | 1,772 → 1,772 | 0 / 1,019 | OK / OK | — (preserved verbatim) |
| **Total** | **All 82 Files** | **75,221** | **13,612** | **-61,609 (-81.90%)** | **5,825,527 → 1,008,203 (-82.69%)** | **58,365 → 2,498** | **361 / 1,542** | **100% / 100%** | **HIGH 17 / MED 29** |

---

## 3. Implicit Typeclass Inference Ambiguity (Diamond / Non-Canonical Instance) Risk Audit

Inference risks that **must be audited and mitigated** when applying de-elaboration against a live Mathlib `v4.33.1` build were automatically classified into three tiers:

1. **HIGH RISK (17 files, 809 occurrences detected) — Stripping Non-Global Custom Local Instances**:
   - `GlobalTheory.LocalData.complRel` (192 occurrences) and `GlobalTheory.LocalData.isLocalField` (12 occurrences): explicitly passed as `ValuativeRel` / `IsNonarchimedeanLocalField` arguments in `FixPiIff.lean`. Because the original file lacks `attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField` at the top, **that single line must be added to the file header** when applying de-elaboration (empirically demonstrated in the standalone harness `verify_01_FixPiIff.lean`).
   - Project-internal auxiliary instances `UpperTheory.Reformulated.B.*.aux*` / `algRes` / `inst*` (605 occurrences): for example, `Qi13.aux1` (`IsLocalRing`) and `Qi13.algRes` (`Algebra (ZMod l) (ResidueField ...)`) in `MemOfClosed.lean`, and `aux6`/`aux7`/`aux11`/`aux12` in `CovariantDegrees.lean`, are declared as plain `theorem`/`def` rather than global instances. Production rollout requires either `attribute [local instance]` annotations or `letI` activation.
2. **MEDIUM RISK (29 files, 3,076 occurrences detected) — Mathlib Diamond-Sensitive Typeclass Families**:
   - `ValuativeRel` / `IsNonarchimedeanLocalField` / `ValuationSubring` (1,492 occurrences): potential overlapping synthesis paths between the valuation ring of `adicCompletion` and `IsDiscreteValuationRing.toIsLocalRing`.
   - `Algebra` / `IsScalarTower` / `SMulCommClass` / `IsAlgClosure` (719 occurrences): whenever a local `RingHom.toAlgebra` instance intervenes — such as `j.toAlgebra : Algebra Ω (PadicAlgCl l)` in `CovariantDegrees.lean::aux11` — implicit synthesis of `IsScalarTower Rat Ω (PadicAlgCl l)` can fail, making it essential to keep `letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra`.
   - `TopologicalSpace` / `UniformSpace` / `MeasurableSpace` / `MeasureTheory.Lp` (414 occurrences) and `NormedRing` / `NormedAddCommGroup` / `CStarAlgebra` (413 occurrences): diamond hazard between `instMeasurableSpaceUJ` (`borel`) and the normed/inner-product space instances of `MeasureTheory.Lp` in `Re3`/`Re4` (`ComplexNormedInstanceCompat`, `HloweqTransfer`); `attribute [local instance] instMeasurableSpaceUJ` is preserved verbatim.
   - `CharP` / `HasQuotient` (38 occurrences): `Submodule.hasQuotient` vs. `Ideal.instHasQuotient_1` in `FreeModuleQuotient.lean`.
3. **LOW RISK (9,611 Tier-2 heads, 13,886 `_` slots)**:
   - Unregistered Mathlib heads (`@RestrictedProduct.evalRingHom`, `@AlgHom.restrictNormal'`, `@MeasureTheory.Lp`, etc.) keep `@Head` and positional arity intact while replacing only purely synthesized dictionary arguments with `_`. Only the rare sites where the Mathlib elaborator lacks enough type context to unify `_` need explicit restoration.

---

## 4. Compilation Results for 5 Structurally Distinct Standalone Lean 4.34.1 Core Verification Harnesses (`exit 0`)

Every harness compiles under `elan run leanprover/lean4:v4.34.1 lean <file>` with **0 Mathlib imports, 0 `sorry`, 0 `axiom`, and 0 `admit`**, and directly proves **kernel definitional equality (`:= rfl`) between the explicit `pp.explicit` version and the de-elaborated version**.

| # | Harness File | Corresponding Original Module · Declarations | Structural Pattern Verified | Code Lines | Kernel `rfl` Equivalence Proofs | `v4.34.1` Result |
| ---: | :--- | :--- | :--- | ---: | :--- | :---: |
| 1 | [verify_01_FixPiIff.lean](../harnesses/verify_01_FixPiIff.lean) | `CI.FixPiIff :: Gr34.mem_UC` (8,001L) | `Field → ValuativeRel → ValuationInt → ResidueField → Units → Subgroup` + `local instance` hazard demo | 299L | `mem_UC_type_defeq : rfl` | **`exit 0`** (0 err, 0 warn) |
| 2 | [verify_02_CovariantDegrees.lean](../harnesses/verify_02_CovariantDegrees.lean) | `CI.CovariantDegrees :: jE`, `conj_invariant_character_transport` (878L), `rHom` (778L) | `RingHom` / `Algebra` / `AlgAut` / `MonHom` signatures + `def` body de-elaboration | 142L | `jE_defeq : rfl`, `conj_transport_defeq : rfl` | **`exit 0`** (0 err, 0 warn) |
| 3 | [verify_03_MemOfClosed.lean](../harnesses/verify_03_MemOfClosed.lean) | `CI.MemOfClosed :: Qi13.aux8` (910L), `Qi13.blift` (1,237L) | Simultaneous `def` body (`Classical.choose`) + `theorem` signature de-elaboration (`aux1` local instance) | 120L | `aux8_defeq : rfl`, `blift_defeq : rfl` | **`exit 0`** (0 err, 0 warn) |
| 4 | [verify_04_MulMemIntA.lean](../harnesses/verify_04_MulMemIntA.lean) | `CI.MulMemIntA :: Uc13.aux4` (2,650L), `Uc13.mul_mem_intA` (1,364L) | `FiniteAdeleRing` / `TensorProduct` / subalgebra closure double induction (`IntA`) | 155L | `aux4_defeq : rfl`, `mul_mem_intA_defeq : rfl` | **`exit 0`** (0 err, 0 warn) |
| 5 | [verify_05_Re3Re4_unified.lean](../harnesses/verify_05_Re3Re4_unified.lean) | `CI.ComplexNormedInstanceCompat` (`Re3`, 3,669L) + `CI.HloweqTransfer` (`Re4`, 3,658L) | Twin-file deduplication + `CStarAlgebra` / `NormedAddCommGroup` / `InnerProductSpace` de-elaboration + compatibility aliases | 191L | `hloweq_type_defeq : rfl` | **`exit 0`** (0 err, 0 warn) |
