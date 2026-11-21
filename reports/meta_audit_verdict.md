# Round 2 Deep Audit Report: Zero-Blind-Spot Metaprogramming & Mathematical Edge-Case Final Verdict (Track A)

> **Language**: English ([한국어 원문](ko/meta_audit_verdict.md))

- **Audit Role**: `meta_auditor` (Track A — Zero-Blind-Spot Deep Auditor)
- **Audit Target**: `../lean/src/` (Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, 175,187 modules total)
- **Foundational Artifacts & Index**:
  - `../out/lean_index.duckdb`
  - `../out/deep_audit.md`
  - `../out/deep_audit_results.json`
  - Lean 4 kernel/elaborator internal call-chain cross-reference: local official `v4.34.1` standard library (`../lean-toolchain/src/lean/Lean/{AddDecl,Environment,LibrarySuggestions/Basic}.lean`)
- **Methodology Compliance**: Original `downloads/lean/src/` unmodified, `lake build` not executed, global `rg`/`grep` over `src/` not executed, and every finding cites exact file paths, line numbers, and verbatim source excerpts.

---

## 0. Executive Verdict

### **Final Verdict: `CLEAN` — 0 Static Blind Spots (Full Metaprogramming, Special-Declaration, and RH/GRH Edge-Case Audit Passed)**

Every metaprogramming construct and non-routine declaration or option detected with a non-zero count by the Round 1 scanner (`deep_audit.py`) was inspected 100% line-by-line from raw source, and all analytic number theory edge cases of the 5 final theorems in `Main.lean` along with the isolation of `SmallClassNumbers.CorGKOf` were cross-verified. The audit confirms **0 pathways to bypass the Lean 4 trusted kernel typechecker or inject hidden axioms, and 0 vacuous mathematical loopholes in the RH/GRH statements or their reduction proofs**.

| Audit Area | Total Hits | Line-by-Line Coverage | Kernel Bypass / Axiom Injection Possibility | In `Main` / `MainTheorems` Cone? | Verdict |
| :--- | ---: | ---: | :--- | :--- | :--- |
| `CutCptCopy.lean` (`addDecl` ×2, `partial def` ×1, `elab` ×1) | 1 module (91 lines) | **100%** | **Impossible** (submits only `.defnDecl`/`.thmDecl` → C++ `lean_add_decl` verification; 0 `debug.skipKernelTC`) | In module cone (`Main` depth 17, `MainTheorems` depth 14); **dynamically generated theorem (`block_growth_bound_of_compact_coefCpt`) is actually consumed at `FinalS.lean:61`** | **CLEAN** |
| `BuildAid/D1..D5.lean` (`run_cmd` / `modifyEnv`, 5 each) | 5 modules (4 lines each) | **100%** | **Impossible** (only appends strings to `LibrarySuggestions.nameDenyListExt`; no access to the kernel constant table) | In module cone (depth 5–18 from `MainTheorems`), 0 declarations, 0 proof-term contribution | **CLEAN** |
| Repo-wide `elab` (3 modules) | 4 hits | **100%** | **Impossible** (`cpt_copy_thms`, `kexactB`, and `kcopy` all require final kernel checking; `#kcopy_probe` is a read-only, uninvoked diagnostic command) | In module cone (`Imports` depth 4, `OwnStruct` depth 6, `CutCptCopy` depth 14 from `MainTheorems`), no elaborator code in proof terms | **CLEAN** |
| Repo-wide `partial def` (2 modules) | 2 hits | **100%** | **Impossible** (compile-time meta-functions only; Lean 4 `partial def` itself is sound as kernel `opaque`) | In module cone, **0** occurrences in kernel proof terms | **CLEAN** |
| Global `macro` (19 modules) | 22 hits | **100%** | **Impossible** (all 22 are `: tactic =>` tactic shorthands; 0 shadowing) | 19/19 modules in `MainTheorems` cone | **CLEAN** |
| `allowUnsafeReducibility` | 37 hits | **100%** | **Impossible** (all 37/37 solely attach `attribute [local irreducible]`, an elaborator transparency option) | In module cone (`DB_Rch` 37/37) | **CLEAN** |
| `hygiene` | 31 hits | **100%** | **Impossible** (all 31/31 are `set_option hygiene false in` + `local notation` 22 / `local macro` 8 / `scoped macro` 1) | In module cone (`DB_Rch` 31/31) | **CLEAN** |
| Other non-routine `set_option` (`quotPrecheck` 7, `smartUnfolding` 3, `Elab.async` 1, `genSizeOf` 1, `warn.classDefReducibility` 1) | 13 hits | **100%** | **Impossible** (across all 33 option kinds / 88,139 total occurrences, **0** `debug.skipKernelTC`/`debug.proofAsSorry`) | In module cone | **CLEAN** |
| RH/GRH mathematical edge cases (`Main` and 8+ files) | 5 final theorems | **100%** | — (`s=0`, `s=-2(n+1)`, `s=1`, `[NeZero N]`, `χ=1` vs `χ≠1`, imprimitive Euler factors, `Re(s)=0,1` all rigorously verified) | 100% match across all 5 theorems in `Main.lean` | **CLEAN** |
| `MainTheoremsAll` → `SmallClassNumbers.CorGKOf` isolation | 4 auxiliary modules | **100%** | — (0 imports of the 4 modules in the `MainTheorems` cone; complete isolation) | Included only in `Main`, **outside the `MainTheorems` cone** | **CLEAN** |

> **Audit Scope Boundary**: This report presents a **100% static, line-by-line source and kernel-architecture deep audit** performed in an environment without a local `leanprover/lean4:v4.33.1` toolchain or `.lake/` build cache. Full binary-level formal certification still requires running `lake build Main` and `#print axioms` on all 5 final theorems in a `v4.33.1` environment.

---

## Part 1. Line-by-Line Exhaustive Audit of Metaprogramming and Special Declarations

### 1.1 Exhaustive Audit of `CutCptCopy.lean` (`addDecl` ×2 · `partial def` ×1 · `elab` ×1)

- **Target Files**:
  - Core implementation (91 lines in full): `../lean/src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean`
  - Sole invocation site: `../lean/src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutMainCpt.lean` (`L1-2`, `L944-945`)
  - Downstream consumers: `../lean/src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CptCopy2.lean` (`L1-159`), `../lean/src/CompanionTheory/AutomorphicTheory/CompactTopologicalForms/FinalS.lean` (`L1-200`)

#### (a) Line-by-Line Behavioral Analysis and Verbatim Key Excerpts

`CutCptCopy.lean` defines a command elaborator `cpt_copy_thms` that traverses the dependency DAG of already-proved `Formalism.FourierDecayAlt.*` theorems, substitutes 3 foundational theorems (`pb_formPos`, `list_duality_level_group`, `vector_isomorphism_levels`) with their compact-support counterparts, and registers the cloned theorems (suffixed with `...Cpt`).

1. **Imports (`L1-10`)**: Imports 6 source-theorem modules (`CutLimENFMain`, `CutGermDone`, `CutNFTopFormDone`, `CutNFIdPairPtw`, `CutNFIdPolAll`, `CutNFTopPtw`) and 4 compact-support replacement-theorem modules (`ModuleFormPosCompactSupport`, `VectorIsomorphismCompactSupport`, `SizeStandardCompact`, `ExistsNormBoundThreeFamilies`).
2. **Substitution Specification (`L16-36`)**:
   - `special` (`L16-19`): 1-to-1 mapping of the 3 base theorems to their compact-support versions:
     ```lean
     def special : List (Name × Name) :=
       [(`Formalism.FourierDecayAlt.P.pb_formPos, `Formalism.FourierDecayAlt.P.module_form_pos_compact_support),
        (`Formalism.FourierDecayAlt.P.list_duality_level_group, `Formalism.FourierDecayAlt.P.size_standard_compact),
        (`Formalism.FourierDecayAlt.P.vector_isomorphism_levels, `Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support)]
     ```
   - `manual` (`L21-26`): List of 14 boundary declarations whose `...Cpt` versions were written manually (`ThmPActual`, `SizeStd`, `VIso`, `FormPos`, `standard_pairing_of_heads`, `FormNonneg`, `form_re_nonneg`, `form_cs`, `formNonneg_of`, `posAt_of_cpt`, `integral_three_at_place_of_parts`, `integral_four_at_place_of_parts`, `truncated_limit_positivity_holds`, `glGram`; these correspond to `CutCptManual.lean` etc., imported at `CutMainCpt.lean:1`).
   - `roots` (`L28-30`): 6 top-level root theorems for the cloning traversal:
     ```lean
     def roots : List Name :=
       [`Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main4, `Formalism.FourierDecayAlt.P.CutBP.germ_truncation_positive, `Formalism.FourierDecayAlt.P.CutBP.block_growth_bound_of_compact_coef,
        `Formalism.FourierDecayAlt.P.CutBP.nFTopFormAll_of_ptw, `Formalism.FourierDecayAlt.P.CutBP.top_identity_of_domination_limits, `Formalism.FourierDecayAlt.P.CutBP.nfPolFormAll_of_top]
     ```
   - `terminal` (`L32`): `manual.contains n || (special.lookup n).isSome` — traversal stopping-boundary predicate.
   - `suffixed` (`L34-36`): Appends the `"Cpt"` suffix to a declaration name.
3. **Constant Collection and Post-Order Topological DFS (`L38-56`)**:
   ```lean
   def proposals (ci : ConstantInfo) : Array Name :=
     ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])

   partial def go (env : Environment) (n : Name) (st : NameSet × NameSet × Array Name) : NameSet × NameSet × Array Name :=
     let (seen, tainted, order) := st
     if seen.contains n || terminal n then st else
     let seen := seen.insert n
     match env.find? n with
     | none => (seen, tainted, order)
     | some ci =>
       let us := proposals ci
       let (seen, tainted, order) :=
         us.foldl (fun s c => if (`Formalism).isPrefixOf c then go env c s else s) (seen, tainted, order)
       if us.any (fun c => terminal c || tainted.contains c) then (seen, tainted.insert n, order.push n)
       else (seen, tainted, order)

   def toCopy (env : Environment) : NameSet × Array Name :=
     let (_, tainted, order) := roots.foldl (fun s r => go env r s) ({}, {}, #[])
     (tainted, order)
   ```
   - `allowOpaque := true` in `proposals` (`L38-39`) is used exclusively for **read-only** dependency-constant collection; actual environment registration (`L76-84`) explicitly rejects `.opaqueInfo`.
   - `go` (`L41-52`) recursively visits only constants under the `Formalism` prefix and accumulates solely constants that directly or indirectly depend on `terminal` into the `tainted` set and topologically ordered array `order`.
4. **Expression Substitution and Declaration Registration (`L58-89`)**:
   ```lean
   def mapName (tainted : NameSet) (n : Name) : Name :=
     match special.lookup n with
     | some m => m
     | none => if manual.contains n || tainted.contains n then suffixed n else n

   def subst (tainted : NameSet) (e : Expr) : Expr :=
     e.replace fun
       | .const n ls => some (.const (mapName tainted n) ls)
       | _ => none

   def copyAll (defsOnly : Bool) : CoreM Nat := do
     let (tainted, order) := toCopy (← getEnv)
     let mut k := 0
     for n in order do
       let env ← getEnv
       let n' := mapName tainted n
       if env.contains n' then continue
       let some ci := env.find? n | throwError "missing {n}"
       match ci with
       | .defnInfo d =>
         addDecl (.defnDecl { d with name := n', type := subst tainted d.type, value := subst tainted d.value })
         k := k + 1
       | .thmInfo t =>
         if defsOnly then continue
         addDecl (.thmDecl { t with name := n', type := subst tainted t.type, value := subst tainted t.value })
         k := k + 1
       | _ => throwError "cannot copy {n}"
     return k

   elab "cpt_copy_thms" : command => do
     let k ← liftCoreM (copyAll false)
     logInfo m!"copied {k} declarations"
   ```
   - **Sole invocation site (`CutMainCpt.lean:944-945`)**:
     ```lean
     set_option maxHeartbeats 0 in
     cpt_copy_thms
     ```
   - **Empirical verification of dynamic generation and consumption**: Cross-checking DuckDB `decls` shows that among the 6 `roots`, `thmBpAt_main4Cpt` is already statically declared at `CutMainCpt.lean:475` and is therefore skipped at `L74` (`if env.contains n' then continue`). By contrast, the remaining 5 root counterparts (`germ_truncation_positiveCpt`, `block_growth_bound_of_compact_coefCpt`, `nFTopFormAll_of_ptwCpt`, `top_identity_of_domination_limitsCpt`, `nfPolFormAll_of_topCpt`) do not appear in static source and are **dynamically generated by `cpt_copy_thms` at `CutMainCpt.lean:945`**. Furthermore, `FinalS.lean:61` directly invokes `block_growth_bound_of_compact_coefCpt`:
     ```lean
     -- CompanionTheory/AutomorphicTheory/CompactTopologicalForms/FinalS.lean:60-61
     ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N := fun _ hε n =>
       block_growth_bound_of_compact_coefCpt hA p nn _ Y K N Cb hCb (cptCoef_apx P p.T.base hχ hF hε n) hnn
     ```

#### (b) Technical Justification: Impossibility of Bypassing the Lean 4 Kernel / Elaborator

1. **Mandatory passage through the trusted C++ kernel typechecker**: `Lean.addDecl`, called at `CutCptCopy.lean:78,82`, is not an elaborator shortcut; it is the standard registration API used by every `def` and `theorem` in Lean 4. Per the Lean 4 standard library sources (`Lean/AddDecl.lean`, `Lean/Environment.lean`), the exact call chain is:
   - `Lean.addDecl` (`AddDecl.lean:229-230`) → `addDeclCore` (`AddDecl.lean:101-194`)
   - Inside `doAdd`, calls `(← getEnv).addDeclAux (← getOptions) decl ...` (`AddDecl.lean:188`)
   - `Environment.addDeclAux` (`AddDecl.lean:30-33`) → `env.addDeclCore ... (!debug.skipKernelTC.get opts)`
   - `Environment.addDeclCore` (`Environment.lean:701-711`): when `doCheck = true`, calls `addDeclCheck` → `Kernel.Environment.addDeclCore` (`@[extern "lean_add_decl"]`, `Environment.lean:296-298`), i.e., the **trusted C++ kernel typechecker**.
   - Note that the `catch ex => addAsAxiom; throw ex` clause in `addDeclCore` (`AddDecl.lean:191-194`) temporarily registers a placeholder solely to prevent cascading IDE error floods after a kernel verification failure and **immediately rethrows `ex`**, so any declaration failing kernel verification aborts compilation with an error.
2. **All kernel-check bypass paths confirmed completely blocked**:
   - Unchecked kernel registration API `addDeclWithoutChecking` (`Environment.lean:307-308`): **0 hits** across all 175,187 files.
   - Kernel-checking disable option `debug.skipKernelTC`: **0 hits** across all 88,139 `set_option` directives (33 kinds) and `lakefile.toml`.
   - `set_option maxHeartbeats 0 in` at `CutMainCpt.lean:944` lifts only the timeout budget while sequentially typechecking many theorems inside a single command; it has zero effect on the `doCheck` flag or kernel typechecking rules.
3. **Complete structural block on axiom / opaque-constant injection**: `copyAll` (`L76-84`) submits exclusively `.defnInfo` → `Declaration.defnDecl` (`L78`) and `.thmInfo` → `Declaration.thmDecl` (`L82`), terminating with an error on every other case (`.axiomInfo`, `.opaqueInfo`, `.inductInfo`, `.quotInfo`, etc.) via `L84` (`| _ => throwError "cannot copy {n}"`). Moreover, even a single type or universe mismatch between the `subst tainted`-rewritten `type` and `value` is immediately rejected by C++ `lean_add_decl` with `(kernel) declaration type mismatch`.

#### (c) Exact Dependency Footprint

- **Module import cone**: Reachable from `Main` (depth **17**) and `Supplements.Kernels.MainTheorems` (depth **14**).
  - Shortest path from `MainTheorems` (14 hops):
    `Supplements.Kernels.MainTheorems` → `Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion` → `Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter` → `Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMainEqPOfSiegelWeil` → `CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed` → `CompanionTheory.AutomorphicTheory.BesselWaveGrids.ThmBFinal` → `...WeightedBoundRotatedUniformOfHypsG` → `...WeightedBoundRotatedUniformOfCubicThreshold` → `...EndpointDifferentTypesThreshold` → `CompanionTheory.AutomorphicTheory.CompactTopologicalForms.NormalFormTopDomination` → `...FinalC` → `...FinalS` → `Formalism.HermitianCurvature.HermitianCurvatureProofs.CptCopy2` → `...CutMainCpt` → `...CutCptCopy`
- **Kernel proof-term cone distinction**: None of `CutCptCopy`'s metaprogramming functions (`go`, `copyAll`, `cpt_copy_thms`) appear in the proof terms of `Main`'s 5 theorems. Conversely, the dynamically generated theorems created by `cpt_copy_thms` at `CutMainCpt.lean:945` (such as `block_growth_bound_of_compact_coefCpt`) do enter the proof-term cone of `Main`'s 5 theorems via `FinalS.lean:61`, and every single generated theorem must individually pass formal verification by the C++ kernel `lean_add_decl` before entering the environment.

---

### 1.2 Exhaustive Audit of `BuildAid/D1.lean` – `BuildAid/D5.lean` (`run_cmd` / `modifyEnv`, 5 each)

DuckDB confirms that the `BuildAid` directory contains exactly the 5 files `D1.lean`–`D5.lean`, each exactly 4 lines long with 0 declarations (`decl_count = 0`).

#### (a) Full Verbatim Source of All 5 Files and Line-by-Line Behavior

- `../lean/src/BuildAid/D1.lean` (`L1-4`):
  ```lean
  import Lean.LibrarySuggestions.Basic
  import Lean.Elab.Command

  run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CompanionTheory"
  ```
- `../lean/src/BuildAid/D2.lean` (`L1-4`):
  ```lean
  import Lean.LibrarySuggestions.Basic
  import Lean.Elab.Command

  run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CrystallineSemistableComparison"
  ```
- `../lean/src/BuildAid/D3.lean` (`L1-4`):
  ```lean
  import Lean.LibrarySuggestions.Basic
  import Lean.Elab.Command

  run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "GlobalTheory"
  ```
- `../lean/src/BuildAid/D4.lean` (`L1-4`):
  ```lean
  import Lean.LibrarySuggestions.Basic
  import Lean.Elab.Command

  run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PositivityTheory"
  ```
- `../lean/src/BuildAid/D5.lean` (`L1-4`):
  ```lean
  import Lean.LibrarySuggestions.Basic
  import Lean.Elab.Command

  run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "UpperTheory"
  ```

This matches **character-for-character the official idiom documented in the Lean 4 standard library** at `Lean/LibrarySuggestions/Basic.lean:311-320`:
```lean
/--
A premise whose name has one of the following components is not retrieved.

Use `run_cmd modifyEnv fun env => nameDenyListExt.addEntry env name` to add a name to the deny list.
-/
builtin_initialize nameDenyListExt : SimplePersistentEnvExtension String (List String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) ["Lake", "Lean", "Internal", "Tactic"]
  }
```
In short, this is purely a developer-ergonomics filter preventing 5 massive internal namespaces from flooding `Lean.LibrarySuggestions` (premise retrieval) candidate lists during development and automated search.

#### (b) Technical Justification: Impossibility of Bypassing the Lean 4 Kernel / Elaborator

- `Lean.LibrarySuggestions.nameDenyListExt` is an auxiliary elaborator environment extension of type `SimplePersistentEnvExtension String (List String)`, referenced solely by the `isDeniedPremise` function at `Lean/LibrarySuggestions/Basic.lean:342`.
- `nameDenyListExt.addEntry env "..."` merely `cons`-es one string onto the front of that extension slot's `List String`; it never accesses or mutates the kernel's `Kernel.Environment.constants` map, axiom set, typechecker options, or reducer (WHNF/isDefEq).

#### (c) Exact Dependency Footprint

All 5 modules lie in the module import cones of `Main` and `Supplements.Kernels.MainTheorems`, but because each contains 0 declarations, they make **zero contribution to kernel proof terms**:

| Module | Registered String | Direct Importers | `Main` Depth | `MainTheorems` Depth | Shortest Entry Path from `MainTheorems` (tail) |
| :--- | :--- | ---: | ---: | ---: | :--- |
| `BuildAid.D1` | `"CompanionTheory"` | 3 | 13 | 12 | `... → EmbeddingMiddleFactorTriple → MidExact → BuildAid.D1` |
| `BuildAid.D2` | `"CrystallineSemistableComparison"` | 4 | 12 | 11 | `... → HtOf → Half1 → H1LiftNaturality → BuildAid.D2` |
| `BuildAid.D3` | `"GlobalTheory"` | 25 | 8 | 5 | `MainTheorems → MainConclusion → RiemannHypothesisOfEveryCharacter → BkLawEntriesStatement → NonzeroPlacesOverPrimesLifts → BuildAid.D3` |
| `BuildAid.D4` | `"PositivityTheory"` | 5 | 8 | 6 | `MainTheorems → MainConclusion → EveryCharacterOfLiteratureOfVWin → LanglandsMultisegmentsOfSeg → EmbeddingMiddleFactorTriple → MidExact → BuildAid.D4` |
| `BuildAid.D5` | `"UpperTheory"` | 1 | 19 | 18 | `... → ThetaLiftOfZel → ImportsAlt → MNolow → MFront → BuildAid.D5` |

---

### 1.3 Exhaustive Audit of All 4 Repository-Wide `elab` Declarations (All 3 Files Read in Full)

Per the Round 1 scan (`deep_audit_results.json`), the total number of `elab` / `elab_rules` declarations across all 175,187 files is **exact count 4 (across 3 modules)**. (`elab_rules`: 0 hits; `syntax`: 0 hits.)

#### (1) `CutCptCopy.lean:87-89` — `elab "cpt_copy_thms" : command`
- Audited in full in Section 1.1 above (**CLEAN**).

#### (2) `Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean:1-8` — `elab "kexactB " e:term : tactic`

- **(a) Full Verbatim Source and Line-by-Line Behavior**:
  ```lean
  import Lean

  open Lean Elab Tactic Meta

  elab "kexactB " e:term : tactic => withMainContext do
    let g ← getMainGoal
    let v ← Term.elabTermAndSynthesize e none
    g.assign (← instantiateMVars v)
  ```
  - `L5`: Defines the `kexactB <term>` tactic, entering the current main goal's `LocalContext` via `withMainContext`.
  - `L6`: Retrieves the current main goal metavariable `g : MVarId`.
  - `L7`: Elaborates and synthesizes typeclass instances for term `e` with no expected type (`expectedType? := none`) via `Term.elabTermAndSynthesize e none`.
  - `L8`: Instantiates metavariables and directly assigns term `v` to goal metavariable `g` via `g.assign`.
  - **Verified call sites**:
    - `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/PlaceModelImp.lean:27`: `scoped macro:max "kc% " e:term:max : term => `((by kexactB $e))`
    - `Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwoLeMOf.lean:72-79`: `local macro:max "kd% " e:term:max : term => `((by kexactB $e))` and structure field transfers (`isom := (by kexactB ($d).isom)`, etc.)
    - `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ECure.lean:58`: `by kexactB LinearIsometryEquiv.refl ℂ (ColT (h.shInj u))`

- **(b) Technical Justification: Impossibility of Bypassing the Lean 4 Kernel / Elaborator**:
  - Standard `exact e` pre-checks definitional equality between `inferType v` and `g.getType` using the elaborator's `Meta.isDefEq`, which can suffer heartbeat blowup on deeply nested structures. `kexactB` **skips only this elaborator-stage preliminary `isDefEq` check**, assigning `g := v` in the `MetavarContext`.
  - However, once elaboration of the enclosing `theorem`/`def` finishes, Lean 4 submits the entire assembled closed proof term to `Lean.addDecl` → C++ kernel `lean_add_decl`. The C++ kernel never trusts the elaborator's `MetavarContext` or `g.assign` history: it independently typechecks the final closed `Expr` from scratch, and if `v`'s type fails kernel `is_def_eq` against the target type, it immediately rejects the declaration with `(kernel) declaration type mismatch`.
  - `kexactB` never modifies the `Environment`, never invokes any `sorryAx`-producing API, and elaborates its input `e` normally via `Term.elabTermAndSynthesize`.

- **(c) Exact Dependency Footprint**:
  - **45** direct importer modules.
  - `Main` depth **7**, `Supplements.Kernels.MainTheorems` depth **4**:
    `MainTheorems` → `MainConclusion` → `RiemannHypothesisOfEveryCharacter` → `TwoLeMOf` → `Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports`.
  - Although the module lies in the import cone, the tactic elaborator `kexactB` itself does not persist in kernel proof terms.

#### (3) & (4) `Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:1-66` — `elab "kcopy "` (`L53-58`) and `elab "#kcopy_probe "` (`L60-64`)

- **(a) Full Summary and Verbatim Key Excerpts**:
  - `kdefeq` (`L7-13`): When `a` and `b` contain no unresolved metavariables, performs a **read-only** call to `Kernel.isDefEq (← getEnv) (← getLCtx) a b` and returns the kernel definitional-equality `Bool`.
  - `ownStruct` (`L15-16`): Checks whether `isStructure env S` holds and either the root namespace is `Formalism` or `S` is one of 7 core tuple/logic structures (``And``, ``Prod``, ``PProd``, ``Sigma``, ``PSigma``, ``Subtype``, ``Iff``).
  - `partial def copyAt` (`L18-51`): (See Section 1.4 for details.) If the target type `tgt` is a function type (`.forallE`), performs $\eta$-expansion via `withLocalDecl` + `mkLambdaFVars`; if `ownStruct env S` holds, applies the structure constructor `mkConst ctor.name us` to its parameters and recursively rebuilds each field extracted via `Expr.proj S i e` (with `fuel` decrementing from 64; only when `probe = true` does it call `kdefeq` and `whnf` to log mismatch paths into a diagnostic array).
  - Both `elab` declarations (`L53-64`):
    ```lean
    elab "kcopy " t:term : tactic => withMainContext do
      let g ← getMainGoal
      let tgt ← instantiateMVars (← g.getType)
      let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
      let (v, _) ← (copyAt false e tgt "" 64).run #[]
      g.assign (← instantiateMVars v)

    elab "#kcopy_probe " t:term " : " ty:term : command => Command.runTermElabM fun _ => do
      let tgt ← instantiateMVars (← Term.elabType ty)
      let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
      let (_, bad) ← (copyAt true e tgt "" 64).run #[]
      logInfo m!"kcopy_probe: {bad.size} refused: {bad.toList}"
    ```
  - **Exhaustive check of all 4 direct importers**:
    - `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsKeptChoiceUpperLattice.lean:26`: `by kcopy n.tp`, `by kcopy n.tie`, `by kcopy n.chrPsi`
    - `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FormsRe.lean:20`: `by kcopy T`
    - `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HermRe.lean:19`: `by kcopy H`
    - `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsColsTiedSym.lean:4`: import only
    - **`#kcopy_probe` has 0 invocations across the entire repository** (an unused diagnostic command left over from debugging).

- **(b) Technical Justification: Impossibility of Bypassing the Lean 4 Kernel / Elaborator**:
  - `kcopy` synthesizes purely core kernel expressions (`.lam`, `.app`, `.const`, `.proj`) via `copyAt false` and assigns the result to the goal metavariable via `g.assign`. Just like `kexactB`, it leaves the `Environment` untouched, and the entire $\eta$-expanded proof term must pass independent typechecking in the C++ kernel `lean_add_decl` upon declaration registration. Any incompatibility between the structure types or fields of `e` and `tgt` is immediately rejected by the kernel.
  - `#kcopy_probe` executes `copyAt true` under `Command.runTermElabM` and prints diagnostic text via `logInfo` without adding any declaration to the environment, and is never invoked anywhere in the repository.

- **(c) Exact Dependency Footprint**:
  - **4** direct importer modules.
  - `Main` depth **9**, `Supplements.Kernels.MainTheorems` depth **6**:
    `MainTheorems` → `MainConclusion` → `RiemannHypothesisOfEveryCharacter` → `LinkOfClosedAtFamily` → `ExistsKeptChoiceUpperLatticeStatement` → `ExistsKeptChoiceUpperLattice` → `Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct`.
  - Although the module lies in the import cone, none of `kcopy`, `#kcopy_probe`, `copyAt`, or `kdefeq` appear in kernel proof terms.

---

### 1.4 Exhaustive Audit of All 2 Repository-Wide `partial def` Declarations (Both Files Read in Full)

Per `deep_audit_results.json`, the total count of `partial def` (and all `partial` declarations including `partial abbrev`/`instance`/`theorem`) across all 175,187 files is **exact count 2**.

| # | File and Line Range | Declaration Signature | Purpose & Termination Guarantee |
| -: | :--- | :--- | :--- |
| 1 | `Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:41-52` | `partial def go (env : Environment) (n : Name) (st : NameSet × NameSet × Array Name) : NameSet × NameSet × Array Name` | Compile-time post-order DFS over the constant dependency DAG inside `cpt_copy_thms` (immediately guards visited nodes via `seen : NameSet`, guaranteeing termination over any finite `Environment`) |
| 2 | `Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:18-51` | `partial def copyAt (probe : Bool) (e tgt : Expr) (path : String) (fuel : Nat) : StateT (Array String) MetaM Expr` | Compile-time structure $\eta$-expander inside `kcopy`/`#kcopy_probe` (explicit fuel parameter `fuel : Nat := 64` strictly decreases via `fuel - 1` on every recursive call and returns immediately at `fuel = 0`) |

#### Lean 4 Kernel Soundness Argument & Dependency Footprint

1. **Intrinsic soundness of `partial def` in the Lean 4 kernel**: Lean 4 never adds a `partial def f : α → β := body` to the logical kernel as a non-terminating recursive axiom. Instead, it requires an `Inhabited`/`Nonempty` witness for the codomain `β` and registers `f` in the kernel as an **`opaque` constant** (making it impossible to inhabit `Empty` or `False`). The kernel cannot unfold `f`'s recursive equations at all; `body` is used exclusively by the compiler/VM (e.g., elaborator metacode).
2. **Complete meta-level isolation**: Furthermore, both `partial def` declarations in this repository are **pure compile-time meta-functions** operating on `Environment`/`NameSet` and `MetaM Expr`—completely unrelated to mathematical types (`ℂ`, `DirichletCharacter`, etc.)—and appear **0 times** in the kernel proof terms of `Main`'s 5 final theorems.
3. **Module import cone**: Both enter the module import cone via `CutCptCopy` (`MainTheorems` depth 14) and `OwnStruct` (`MainTheorems` depth 6), but are absent from the kernel proof-term cone.

---

### 1.5 Exhaustive (100%) Audit of Global `macro` (22) · `allowUnsafeReducibility` (37) · `hygiene` (31) · Other Non-Routine `set_option` (13)

Going beyond Round 1 sampling, this deep audit inspected directly from disk 100% of the raw source context for **all 22/22 global `macro` declarations**, **all 37/37 `allowUnsafeReducibility` occurrences**, **all 31/31 `hygiene` occurrences**, and **all 13/13 other non-routine `set_option` occurrences** recorded in `deep_audit_results.json`.

#### (1) Exhaustive Verification Table of All 22/22 Global `macro` Definitions (19 Modules, All in `MainTheorems` Cone)

**All 22 are `: tactic =>` tactic shorthands**; there are **0** term (`: term`), command (`: command`), or notation macros. None shadows any Lean/Mathlib primitive keyword or `Statements.lean`/`Main.lean` identifier, and every expansion reduces to ordinary tactics (`simp`, `omega`, `ring`, `grind`, `linarith`, `module`, `apply`, `erw`, `exact`, etc.) that undergo standard kernel typechecking.

| # | File Path (`src/...`) | Line | Macro Name | Category | Core Expansion (Verified from Source) |
| -: | :--- | ---: | :--- | :--- | :--- |
| 1 | `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/NegOnePowBoundaryTermsCancel.lean` | 114 | `fin_index_simp` | `: tactic` | `simp (disch := ... omega) only [Fin.val_*, ...]; try omega` |
| 2 | `Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperOfFiniteType.lean` | 30 | `lbt` | `: tactic` | `repeat (first \| assumption \| apply pull_isLB)` |
| 3 | `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RigidFrameSymmetricRatioSeries.lean` | 49 | `jet_tac` | `: tactic` | `refine jet_ext ...; simp only [...]; refine congrArg _ ?_; simp [...]; try ring` |
| 4 | `Development/AutomorphicSpectrum/Proofs/BlockDecomposition/Cup1CoboundaryMemBoundaries.lean` | 96 | `fin_order` | `: tactic` | `apply Fin.ext; simp only [OrderHom.comp_coe, ...]; grind` |
| 5 | `Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleCup1FormulaPositiveDegree.lean` | 29 | `fin_order'` | `: tactic` | `apply Fin.ext; simp only [OrderHom.comp_coe, val_sI, ...]; grind` |
| 6 | `Development/EtaleCohomology/EtaleSheaves/ChasePf.lean` | 105 | `meq` | `: tactic` | `first \| (apply pullback.hom_ext <;> rw [← cancel_mono ...] <;> simp [...]) \| ...` |
| 7 | `Development/WeilBound/CoreStatements/HodgeTatePoints/CbBase.lean` | 34 | `zz` | `: tactic` | `repeat' with_reducible first \| assumption \| exact Z_pt _ \| ...` |
| 8 | `Development/WeilBound/CoreStatements/HodgeTatePoints/CbBase.lean` | 81 | `evs` | `: tactic` | `simp (disch := zz) only [evm, eva, ...] $[$loc]?` |
| 9 | `Development/WeilBound/CoreStatements/HodgeTatePoints/CcBase.lean` | 42 | `ztac` | `: tactic` | `repeat' (first \| assumption \| exact ZZ_nil \| ...)` |
| 10 | `Development/WeilBound/CoreStatements/HodgeTatePoints/CcBase.lean` | 81 | `evs at h` | `: tactic` | `simp (disch := ztac) only [FGLaw.add, ...] at $h:ident` |
| 11 | `Development/WeilBound/CoreStatements/PadicHodgeComparison/EtaleCohomologyComparison/CechPairings/FaceMapCompSuccAboveCastSucc.lean` | 227 | `fin_tac` | `: tactic` | `funext x; first \| (apply Fin.ext; simp only [...]; split_ifs <;> omega) \| ...` |
| 12 | `Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean` | 66 | `change_aux_intm` | `: tactic` | `repeat (first \| assumption \| apply ofNatB \| apply add_mem \| ...)` |
| 13 | `Formalism/HermitianCurvature/HermitianCurvatureProofs/RttUpperRelationsFromDescent.lean` | 30 | `distrib_module` | `: tactic` | `simp only [mul_sub, sub_mul, ..., smul_smul]; module` |
| 14 | `Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/FunctionalLowerBoundOfConditionsNumeric.lean` | 231 | `pos_tac` | `: tactic` | `(repeat' (first \| positivity \| apply mul_nonneg \| ...)) <;> linarith` |
| 15 | `Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/FunctionalLowerBoundOfConditionsNumeric.lean` | 234 | `onele_tac` | `: tactic` | `(repeat' (first \| exact one_le_pow₀ ... \| apply one_le_mul_of_one_le_of_one_le)) <;> assumption` |
| 16 | `Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/NonsingularNorm.lean` | 70 | `integ` | `: tactic` | `repeat' (first \| assumption \| exact i_ofNat _ \| apply i_add \| ...)` |
| 17 | `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFibreBoundV.lean` | 175 | `nbt` | `: tactic` | `simp only [unipotentBlockMatrix, Matrix.of_apply]; split_ifs <;> ...` |
| 18 | `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaussianUniqueness/MulMApply.lean` | 12 | `lvo` | `: tactic` | `intro a b c h1 h2; (try dsimp only at h1 h2 ⊢); omega` |
| 19 | `Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaC.lean` | 7 | `fIwasawa_omega` | `: tactic` | `(try simp only [Fin.lt_def, ..., not_true_eq_false] at *) <;> omega` |
| 20 | `Formalism/SharpRestriction/Divisibility/LocalNonemptiness/SubsingletonRankIndicatorIff.lean` | 276 | `exists_prescribed_local_data` | `: tactic` | `intros; first \| trivial \| rfl \| exact Subsingleton.elim _ _ \| simp` |
| 21 | `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsRosatiGen.lean` | 34 | `secTac` | `: tactic` | `simp [Sum.forall, Fin.forall_fin_succ, Over.w, ..., Matrix.cons_val_succ]` |
| 22 | `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/Theta1.lean` | 25 | `ones` | `: tactic` | `repeat (first \| erw [map_one] \| erw [one_zpow] \| ... \| erw [_root_.one_mul])` |

*(Note: The remaining 65 local/scoped `macro` definitions likewise consist strictly of local tactic/term shorthands such as `kc%`/`kq%`/`kd%`/`tr_via`/`obt`/`opens_le`/`tie_cases`/`pre_cases`, all of which pass kernel verification after elaboration.)*

#### (2) Exhaustive Verification of All 37/37 `allowUnsafeReducibility` Occurrences

**All 37 occurrences serve exclusively to attach `attribute [local irreducible]` to definitions from other modules**; not a single instance forces `[reducible]` or mutates global attributes:
- **30 hits** (`IsCrisP.lean:49`, `AlgClosureTensorBcrisToBdRInjective.lean:67`, `ExistsPowNorm.lean:86`, etc. across 26 modules under `InertiaEigenvalues`/`IwasawaDecomposition`): `attribute [local irreducible] Per.Acris Per.Bcris` (or `Per.Acris` alone). Notably, the sole file-scoped instance without `in` (`ExistsPowNorm.lean:86-87`) is directly followed by a single line `attribute [local irreducible] Per.Acris Per.Bcris` and then solely ordinary theorems (`homog_eq`, `untilt_zero`, `gauss_l`, etc.), verified directly from source.
- **1 hit** (`ExistsFormFamilyHypothesesChangedSecondNorm.lean:38-40`): `attribute [local irreducible] _root_.NumberField.RingOfIntegers _root_.CommRing.toCommSemiring _root_.NumberField.instCommRingRingOfIntegers _root_.AddCommGroup.toAddCommMonoid`.
- **6 hits** (`AutomorphicInSphericalLevel.lean:218,315`, `CongLev.lean:177`, `EigGen.lean:154`, `FinOrbSubgroupOf.lean:213`, `LevUnion.lean:78`): `attribute [local irreducible] cv Kv Ov DX KD RP SA Lsq ...`.
- **Kernel irrelevance**: The `irreducible` attribute is strictly an elaborator `Meta`-level transparency hint; the C++ kernel ignores `irreducible` attributes and checks definitional equality uniformly across all `def` declarations, so soundness cannot be affected.

#### (3) Exhaustive Verification of All 31/31 `hygiene` Occurrences

**All 31 occurrences use `set_option hygiene false in` (strictly scoped to a single declaration)**, targeting exclusively the following 3 constructs:
- `local notation` — **22 hits** (e.g., `ExistsOrderTwoTranslateEvenCubicalBundle.lean:376-377` `local notation "𝔪" => ...`, `PNormalModelPlace.lean:174-189` `𝒜, ℬ, 𝒪, 𝒪̄, 𝒯, 𝒦, ℱ, 𝔏`, `PJoinDivCycle.lean:53-59` `ψ, ε`, `LocUnrSplit.lean:120-121` `𝟙`, etc. — allowing local notations to reference section variables directly).
- `local macro` — **8 hits** (`FormGroupsModelsActionsMeasuresBasesCharacterise.lean:28,79`, `ReferenceTupleWeilDatumVectorPolynomialMapEnlarg.lean:23,159,211`, `ThetaLiftAtReferenceTupleOverEnlargedBase.lean:51,70,181` — tactic macros `tie_cases`, `pre_cases`, `pre_sub`, `coef_cases` capturing local hypothesis names at the call site).
- `scoped macro` — **1 hit** (`RingSpecNormalisedCharacterEq.lean:73-75` — `scoped macro "copy_cases " h:ident D:ident D':ident : tactic`).
- **Kernel irrelevance**: Macro hygiene governs only identifier capture during parsing and macro expansion; the expanded final proof terms pass through the kernel typechecker identically to ordinary code.

#### (4) Exhaustive Check of All 13/13 Other Non-Routine `set_option` Hits & All 33 Option Kinds (88,139 Total)

- `quotPrecheck false` — **7/7 hits**: All suppress syntax-quotation prechecking for `local notation` (`ExistsUniqueVectorFieldOfGlobalOneFormValues.lean:36`, `TwistedOrbitalSwapConvolution.lean:26,28`, `TuplesP.lean:1433`, `MeasFr.lean:90`, `MeasLev.lean:23`, `SatisfiesGlRelationsBilinearLeft.lean:43` — `local notation "D"`, `"Mx"` inside `section ops`).
- `smartUnfolding false in` — **3/3 hits**: `ECure.lean:18`, `BuDefQEta.lean:123,136` — disables the elaborator's WHNF unfolding heuristic (kernel-irrelevant).
- `Elab.async false in` — **1/1 hit**: `Decomp.lean:167` — disables asynchronous elaboration and forces **synchronous kernel typechecking** (the exact opposite of a kernel bypass).
- `genSizeOf false` — **1/1 hit**: `IsFirstChernClassInJAlt.lean:9` — suppresses automatic `SizeOf` boilerplate generation for a structure.
- `warn.classDefReducibility false in` — **1/1 hit**: `BaseChangeMapMemLattice.lean:34` — suppresses a linter warning on `def bTop`.
- **Complete inventory of all 33 `set_option` kinds (88,139 occurrences)**: `maxHeartbeats` (57,556), `autoImplicit` (11,203), `maxSynthPendingDepth` (7,478), `synthInstance.maxHeartbeats` (7,381), `backward.isDefEq.respectTransparency` (+`.types`, 1,966), `linter.*` (14 options, 1,987), `genSizeOfSpec`/`genInjectivity`/`genSizeOf` (361), `synthInstance.maxSize`/`maxRecDepth` (85), `allowUnsafeReducibility` (37), `backward.defeqAttrib.useBackward` (33), `hygiene` (31), `pp.fullNames` (9), `quotPrecheck` (7), `smartUnfolding` (3), `Elab.async` (1), `warn.classDefReducibility` (1). There are **0 occurrences of `debug.skipKernelTC`, `debug.proofAsSorry`, or any kernel-bypass option**.

---

## Part 2. Deep Audit of Analytic Number Theory Edge Cases (Mathematical Edge-Case Audit)

### 2.1 Definitional Consistency Across `Main.lean` (5 Final Theorems), `Statements.lean`, and Mathlib

Cross-checking `Statements.lean` (`L1`: solely `import Mathlib`), `Main.lean` (`L1-12`), and the core reduction chain (`MainTheorems.lean`, `HalfPlane.lean`, `ClaimStrip.lean`, `CritLine.lean`, `RhOfRight.lean`, `EveryCharacter.lean`, `Imprimitive.lean`) yields the following exact correspondence:

| `Main.lean` Theorem | Declared Type (`Statements.lean` / Mathlib) | Proof Term (`MainTheorems.lean`) | Definitional Equality Verification Basis |
| :--- | :--- | :--- | :--- |
| `Main.riemannHypothesis` (`L4`) | `RiemannHypothesis` (Mathlib standard) | `rhOfAll` (`L9`) | Returns Mathlib `RiemannHypothesis` directly |
| `Main.riemannZeta_eq_zero_re` (`L6`) | `RiemannZetaZerosOnLine` (`Statements.lean:3-4`) | `rhOfAll` (`L9`) | Directly supplies `rhOfAll : RiemannHypothesis` with no coercion + `ClaimStrip.lean:102` `theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl` |
| `Main.LFunction_ne_zero_of_half_lt_re` (`L8`) | `DirichletLNonvanishingRightOfHalf` (`Statements.lean:6-8`) | `allChi` (`L7`) | **Exact character-and-type match** with `UpperTheory.EveryCharacter` (`EveryCharacter.lean:13-14`) and `Claim.HalfPlane` (`HalfPlane.lean:3-4`) |
| `Main.LFunction_eq_zero_re` (`L10`) | `DirichletLZerosOnLine` (`Statements.lean:10-12`) | `claimAll.2.1` (`L15-16`) | **Exact character-and-type match** with `Claim.Strip` (`HalfPlane.lean:6-7`) |
| `Main.LFunction_eq_zero_re_of_isPrimitive` (`L12`) | `PrimitiveDirichletLZerosOnLine` (`Statements.lean:14-16`) | `critAll` (`L11-13`) | **Exact match** with the output type of `Formalism.VW.critLine` (`CritLine.lean:11-27`) |

---

### 2.2 Exhaustive Edge-Case Audit of the Riemann Zeta Function $\zeta(s)$

Verbatim `Statements.lean:3-4`:
```lean
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2
```

1. **Exactness of excluding the trivial zeros $s = -2, -4, -6, \dots$**:
   - In Lean 4, `ℕ` starts at `0`, so as `n : ℕ` ranges over $\mathbb{N}$, `n + 1` ranges over exactly $\{1, 2, 3, \dots\}$, and `-2 * ((n : ℂ) + 1)` denotes precisely the negative even integers $\{-2, -4, -6, \dots\}$.
   - Both `ClaimStrip.lean:102` (`theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl`) and direct proof-term sharing at `Main.lean:4,6` guarantee 100% definitional identity with Mathlib `0df444a3`'s official `RiemannHypothesis` definition.
2. **Boundary case $s = 0$ (NOT excluded; explicitly proved nonzero)**:
   - `¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)` does **not** exclude `s = 0`. Excluding `s = 0` would constitute an improper weakening, whereas in fact **all 3 independent proof paths** derive `s ≠ 0` directly from Mathlib's `riemannZeta_zero` ($\zeta(0) = -1/2 \neq 0$):
     - `Formalism/GammaFactorNonvanishing/RhOfRight.lean:11-14`:
       ```lean
       have hs0 : s ≠ 0 := by
         rintro rfl
         rw [riemannZeta_zero] at hs
         norm_num at hs
       ```
     - `Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:77`:
       ```lean
       have hs0 : s ≠ 0 := fun e => by rw [e, riemannZeta_zero] at hz; norm_num at hz
       ```
     - `Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:219`:
       ```lean
       have hs0 : s ≠ 0 := by rintro rfl; rw [riemannZeta_zero] at hs; norm_num at hs
       ```
   - Likewise, the $s = 0$ singularity of the gamma/cosine factor appearing during functional-equation reflection is discharged without gaps:
     - `RhOfRight.lean:34-59`: From `Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) = 0`, derives `s = -2 * (k : ℂ)` ($k : \mathbb{Z}$) and applies `lt_trichotomy k 0`: $k < 0 \Rightarrow \operatorname{Re}(s) \ge 2$ (contradicting $\operatorname{Re}(s) < 1/2$, `L45-46`), $k = 0 \Rightarrow s = 0$ (contradicting `hs0`, `L47-49`), and $k > 0 \Rightarrow s = -2((k-1)+1)$ (contradicting `htriv`, `L50-58`).
     - `ClaimStrip.lean:85-90` (and `RiemannHypothesisOfEveryCharacter.lean:227-230`): For `n : ℕ` ($s = -2n$) obtained from `Complex.Gammaℝ_eq_zero_iff`, splits via `rcases n with _ | n`, discharging `n = 0` via `hs0` (`L89`) and `n + 1` via `htriv` (`L90`).
3. **Handling of the pole at $s = 1$**:
   - `s ≠ 1` excludes the pole in exact agreement with the standard RH statement and Mathlib's `RiemannHypothesis`.
   - Additional check: In Mathlib `0df444a3`, `riemannZeta 1` is defined as the regularized value matching the Laurent constant term $(\gamma - \log(4\pi))/2$, satisfying both `riemannZeta_one_ne_zero` (directly cited at `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean:196`) and `riemannZeta_ne_zero_of_one_le_re` (directly cited at `ClaimStrip.lean:83,100`). Thus no junk value of `0` at `s = 1` exists to trigger a vacuous contradiction.
4. **Completeness across $\operatorname{Re}(s) \ge 1$ and $\operatorname{Re}(s) \le 0$**:
   - `RhOfRight.lean:8-62` partitions the entire complex plane via `lt_trichotomy s.re (1 / 2)`: $\operatorname{Re}(s) > 1/2$ closes immediately via `hz s hgt hs1` (`L62`), while $\operatorname{Re}(s) < 1/2$ verifies every side condition of `riemannZeta_one_sub` (`∀ n : ℕ, 1 - s ≠ -n` `L22-27`, `1 - s ≠ 1` `L18-21`) and every nonvanishing factor (`h2pi`, `hG`, `hcos` `L31-59`) to derive a contradiction from `hz (1 - s)`.
   - `ClaimStrip.lean:75-100` independently supplies a 3-region proof covering $0 < \operatorname{Re}(s) < 1$ (`Claim.strip` + `LFunction_modOne_eq`), $\operatorname{Re}(s) \ge 1$ (`riemannZeta_ne_zero_of_one_le_re`), and $\operatorname{Re}(s) \le 0$ (`completedRiemannZeta_one_sub` + $\operatorname{Re}(1-s) \ge 1$).

---

### 2.3 Exhaustive Edge-Case Audit of Dirichlet $L$-Functions $L(s, \chi)$ (GRH)

Verbatim `Statements.lean:6-16`:
```lean
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

#### (1) Verification of Excluding Modulus $N = 0$ (`[NeZero N]`)
- All 3 Dirichlet $L$-function statements (`Statements.lean:7,11,15`) and internal definitions (`EveryCharacter.lean:14`, `HalfPlane.lean:4,7`, `Imprimitive.lean:6`, `CritLine.lean:11`, `PrimePairSizeCondition.lean:9`) require the typeclass instance `[NeZero N]`.
- Because `ZMod 0 = ℤ` in Mathlib, `DirichletCharacter ℂ 0` is not a classical Dirichlet character modulo a finite modulus. `[NeZero N]` covers precisely all positive integer moduli $N \ge 1$.

#### (2) Pole at $s = 1$ and Principal ($\chi = 1$) vs Non-Principal ($\chi \neq 1$) Branching (`χ ≠ 1 ∨ s ≠ 1`)
- **Non-principal characters ($\chi \neq 1$, primitive or imprimitive)**: Via `Or.inl hχ`, the condition `(χ ≠ 1 ∨ s ≠ 1)` holds **even at $s = 1$**. Consequently, `Main.LFunction_ne_zero_of_half_lt_re` formally includes Dirichlet's nonvanishing theorem $L(1, \chi) \neq 0$ for every non-principal character.
- **Principal characters ($\chi = 1 \pmod N$, for both $N = 1$ and $N > 1$)**: `χ ≠ 1 ∨ s ≠ 1` reduces strictly to `s ≠ 1`, excluding only the unique simple pole at $s = 1$ while establishing nonvanishing throughout $\operatorname{Re}(s) > 1/2,\ s \neq 1$ (including the line $\operatorname{Re}(s) = 1,\ \operatorname{Im}(s) \neq 0$).
- **Resolution of a key subtlety (`Imprimitive.lean:10-20` vs `ExplicitFormulaErrorOfHostConditions.lean:11-18`)**:
  - The internal theorem `Formalism.HC.ZeroFreeAll` (`ExplicitFormulaErrorOfHostConditions.lean:11-18`) is stated for the primitive-character wrapper `PChar` as `∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0` without a `s ≠ 1` guard, and `Imprimitive.lean:10` invokes it directly:
    ```lean
    -- Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:9-20
    haveI : NeZero χ.conductor := (PChar.of χ).ne
    have hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := h (PChar.of χ) trivial s hs
    have hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
      rcases hχs with hχ | hs1
      · left
        intro h1
        apply hχ
        rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
      · exact Or.inr hs1
    have hrw := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'
    rw [χ.changeLevel_primitiveCharacter] at hrw
    rw [hrw]
    ```
  - Why this is mathematically valid: Because `PChar` enforces primitivity, the only principal instance is `PChar.one` ($N = 1, \chi = 1_1$, `PrimePairSizeCondition.lean:19`), whose $L$-function equals `riemannZeta` by `LFunction_modOne_eq` and is therefore nonzero even at `s = 1` under Mathlib's `riemannZeta_ne_zero_of_one_le_re` / `riemannZeta_one_ne_zero` (`CharFamilyLFunctionNeZeroOfOneLeRe.lean:17-20`, `poleData.lean:196`).
  - Conversely, for an imprimitive principal character $\chi = 1_N$ ($N > 1$), the Laurent constant term at the pole $s = 1$ of $L(1_N, s) = \zeta(s) \prod_{p \mid N}(1 - p^{-s})$ shifts by a derivative term, which is why Mathlib's `DirichletCharacter.LFunction_changeLevel` requires precisely `χ.primitiveCharacter ≠ 1 ∨ s ≠ 1`. `Imprimitive.lean:11-18` rigorously transforms `χ ≠ 1 ∨ s ≠ 1` into `χ.primitiveCharacter ≠ 1 ∨ s ≠ 1` via `χ.changeLevel_primitiveCharacter` and `DirichletCharacter.changeLevel_one` to discharge that hypothesis.

#### (3) Primitive vs Imprimitive Characters, Conductor $\chi.\mathrm{conductor}$, and Euler Factor Nonvanishing
- For any character $\chi$ of modulus $N \ge 1$, `χ.conductor_ne_zero` provides `[NeZero χ.conductor]`, and `χ.conductor_dvd_level` together with `χ.changeLevel_primitiveCharacter` yields via Mathlib's `DirichletCharacter.LFunction_changeLevel`:
  $$L(\chi, s) = L(\chi^*, s) \prod_{p \in N.\mathrm{primeFactors}} \bigl(1 - \chi^*(p)\, p^{-s}\bigr)$$
  (where $\chi^* = \chi.\mathrm{primitiveCharacter}$ is primitive modulo $q = \chi.\mathrm{conductor}$; for $p \mid q$, $\chi^*(p) = 0$ so the factor is $1$, and for $p \mid N,\ p \nmid q$, $|\chi^*(p)| = 1$).
- **Proof of Euler factor nonvanishing throughout $\operatorname{Re}(s) > 0$**:
  - Both `ClaimStrip.lean:7-21` (`Claim.factor_ne_zero`, proved for all $\operatorname{Re}(s) > 0$) and `Imprimitive.lean:21-35` (proved for $\operatorname{Re}(s) > 1/2$) argue for every prime $p \ge 2$ (`hp.one_lt`, `hp.pos`):
    1. Apply `Complex.norm_natCast_cpow_of_pos` + `Real.rpow_lt_one_of_one_lt_of_neg` to obtain $\|p^{-s}\| = p^{-\operatorname{Re}(s)} < 1$,
    2. Apply `DirichletCharacter.norm_le_one` for $\|\chi^*(p)\| \le 1$,
    3. Conclude $\|\chi^*(p) p^{-s}\| \le 1 \cdot p^{-\operatorname{Re}(s)} < 1$, hence $1 - \chi^*(p) p^{-s} \neq 0$.
- **Reduction of imprimitive critical-strip zeros to primitive zeros (`ClaimStrip.lean:23-33` `Claim.prim_zero`)**:
  - Derives `s ≠ 1` from `hs1 : s.re < 1` (`L26`), legitimately invoking `LFunction_changeLevel ... (Or.inr hs)` even for principal $\chi = 1_N$ ($N > 1$) (`L27-28`), and uses Euler-product nonvanishing (`factor_ne_zero`, `L33`) to deduce $L(\chi^*, s) = 0$.

#### (4) Behavior on the Boundary Lines $\operatorname{Re}(s) = 0$ and $\operatorname{Re}(s) = 1$
- **$\operatorname{Re}(s) = 0$ (mathematical necessity of strict inequality `0 < s.re`)**:
  - Any imprimitive character $\chi \pmod N$ (in particular the principal character $\chi = 1_N$ for $N > 1$, where $q = 1 < N$) has, for every prime $p \mid N,\ p \nmid q$, an Euler factor $(1 - \chi^*(p)p^{-s})$ vanishing at
    $$s = \frac{i\bigl(\arg \chi^*(p) + 2\pi k\bigr)}{\log p} \quad (k \in \mathbb{Z}),$$
    producing **infinitely many extraneous zeros on the line $\operatorname{Re}(s) = 0$** (for $\chi = 1_N$, $s = 2\pi i k / \log p$).
  - Furthermore, primitive even characters ($\chi \neq 1,\ \chi(-1) = 1$) also have a trivial zero at $s = 0$ due to the pole of $\Gamma_{\mathbb{R}}(s)$ at $s = 0$.
  - Hence strictly excluding $\operatorname{Re}(s) = 0$ via `0 < s.re` in `DirichletLZerosOnLine` (`Statements.lean:12`) and `PrimitiveDirichletLZerosOnLine` (`Statements.lean:16`) matches the classical GRH formulation **exactly**.
- **$\operatorname{Re}(s) = 1$**:
  - Excluded from the critical-strip statements via `s.re < 1`, while nonvanishing on $\operatorname{Re}(s) = 1$ (except the simple pole of principal characters at $s = 1$) is already fully subsumed by `Main.LFunction_ne_zero_of_half_lt_re` ($\operatorname{Re}(s) > 1/2$).

#### (5) Equivalence of `DirichletCharacter.LFunction χ s` with Classical $L(s, \chi)$ on $s \in (0, 1) \times i\mathbb{R}$ and Functional-Equation Reflection
- In Mathlib `0df444a3`, `DirichletCharacter.LFunction χ s` is the unique analytic continuation agreeing with the Dirichlet series $\sum_{n=1}^{\infty} \chi(n) n^{-s}$ (`LSeries`) for $\operatorname{Re}(s) > 1$ (entire for non-principal $\chi$, simple pole only at $s = 1$ for principal $\chi$), and satisfies `DirichletCharacter.LFunction_eq_completed_div_gammaFactor` ($\Lambda(\chi, s) / \gamma_\chi(s)$) for all $s \neq 0$.
- The open critical strip $0 < \operatorname{Re}(s) < 1$ contains neither the pole $s = 1$ nor any gamma-factor pole $s \in \{0, -1, -2, \dots\}$, so zero Mathlib junk values intervene and the function agrees **pointwise** with classical $L(s, \chi)$.
- **Audit of the critical-strip reflection proofs (`ClaimStrip.lean:35-73` and `CritLine.lean:6-27`)**:
  - Gamma-factor nonvanishing (`Claim.gamma_ne_zero` `L35-40`, `Formalism.VW.gammaFactor_ne_zero` `L6-9`): splits via `χ.even_or_odd`, applying `Complex.Gammaℝ_ne_zero_of_re_pos` to $\Gamma_{\mathbb{R}}(s)$ ($\operatorname{Re}(s) > 0$) for even characters and to $\Gamma_{\mathbb{R}}(s + 1)$ ($\operatorname{Re}(s + 1) > 1 > 0$) for odd characters.
  - Functional-equation reflection (`Claim.prim_reflect` `L42-57`, `Formalism.VW.critLine` `L11-27`): for primitive $\psi$, proves `ψ⁻¹.IsPrimitive` (`isPrimitive_def`, `conductor_inv`), applies `hψ'.completedLFunction_one_sub s` to obtain $\Lambda(\psi, s) = 0 \Rightarrow \Lambda(\psi^{-1}, 1 - s) = 0$, and combines `1 - s ≠ 0` (from `s.re < 1`) with `LFunction_eq_completed_div_gammaFactor` to conclude $L(\psi^{-1}, 1 - s) = 0$.
  - Final contradiction (`ClaimStrip.lean:69-71`, `CritLine.lean:25`): derives `s ≠ 0` → `1 - s ≠ 1` from `0 < s.re` to satisfy `Or.inr ht`, then invokes `HalfPlane`/`EveryCharacter` at $\operatorname{Re}(1 - s) > 1/2$ to complete the contradiction.

---

### 2.4 Isolation Verification of `MainTheoremsAll.lean` → `SmallClassNumbers.CorGKOf`

Tracing `Main.lean`'s import hierarchy down to the leaves yields:
1. `Main.lean:1-2`: `import Statements`, `import Supplements.Kernels.MainTheoremsAll`.
2. `Supplements/Kernels/MainTheoremsAll.lean:1-2` (0 declarations):
   ```lean
   import Supplements.Kernels.MainTheoremsCritical
   import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.CorGKOf
   ```
3. `Supplements/Kernels/MainTheoremsCritical.lean:1-4` (0 declarations):
   ```lean
   import Supplements.Kernels.MainTheorems
   import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree
   import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.LenEqZeroIff
   import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.OnePoint
   ```
4. `Supplements/Kernels/MainTheorems.lean:1-16`: Imports exclusively `CritLine`, `ClaimStrip`, and `MainConclusion`, and defines all 4 proof terms (`allChi`, `rhOfAll`, `critAll`, `claimAll`) used by `Main.lean`'s 5 theorems.

**Complete Mathematical and Database Isolation Verification**:
- All 4 `SmallClassNumbers` module names (`CorGKOf`, `ClassNumberThree`, `LenEqZeroIff`, `OnePoint`) are **pure ASCII strings**. Because the `index_lean.py:21` Unicode `₂` truncation bug identified in Round 1 drops edges only when `dst_module` contains `₂`, every `import` edge targeting these 4 modules across all 175,187 files (including all 394 Unicode `₂` modules) is recorded in DuckDB's `imports` table with 100% completeness.
- Exhaustive DuckDB `imports` query results:
  - Sole importer of `SmallClassNumbers.CorGKOf`: `['Supplements.Kernels.MainTheoremsAll']`
  - Sole importer of `SmallClassNumbers.LenEqZeroIff`: `['Supplements.Kernels.MainTheoremsCritical']`
  - Sole importer of `SmallClassNumbers.OnePoint`: `['Supplements.Kernels.MainTheoremsCritical']`
  - Importers of `SmallClassNumbers.ClassNumberThree`: `['...CorGKOf', '...LenEqZeroIff', 'Supplements.Kernels.MainTheoremsCritical']`
  - Modules among the 420 previously DB-unreachable modules importing any `SmallClassNumbers.*`: **`[]` (0 hits)**.
- **Conclusion**: The set difference between all of `Main` (175,187 modules) and the dependency cone of `Supplements.Kernels.MainTheorems` (175,179 modules) consists of exactly 8 modules (`Main`, `Statements`, `MainTheoremsAll`, `MainTheoremsCritical`, and the 4 `SmallClassNumbers` modules). `SmallClassNumbers.{CorGKOf, ClassNumberThree, LenEqZeroIff, OnePoint}` are companion theorems bundled under `MainTheoremsAll` that build on the same automorphic/Galois infrastructure (`RowSrc`, `TopMainZj`, `DefiniteNHolds`) to additionally prove Selmer/Shafarevich–Tate length upper bounds (`UpperTheory.V.SmallClassNumbers.corGK`, `bound`, `large_of`, `onePoint`) for the class-number-1 quadratic field $K^*_3$ (`classNumber_three : classNumber (Kstar 3) = 1`); their impact on the statements, proof terms, or axiom dependencies of `Main.lean`'s 5 final RH/GRH theorems is **identically 0**.

---

## Part 3. Final Synthesis & Post-Audit Dynamic Verification Procedure

1. **Zero Metaprogramming Blind Spots**: All instances of `CutCptCopy.lean` (`addDecl` ×2), `BuildAid/D1..D5` (`run_cmd`/`modifyEnv` ×5), repository-wide `elab` ×4 (`cpt_copy_thms`, `kexactB`, `kcopy`, `#kcopy_probe`), repository-wide `partial def` ×2 (`go`, `copyAt`), global `macro` 22/22, `allowUnsafeReducibility` 37/37, `hygiene` 31/31, and other non-routine `set_option` 13/13 were audited line-by-line from raw source, confirming zero kernel bypasses, zero axiom injections, and zero symbol shadowing.
2. **Zero Mathematical Edge-Case Blind Spots**: All 5 theorems in `Main.lean` (`riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`) match the classical definitions of RH and GRH 100%, including trivial zeros ($-2,-4,\dots$), explicit nonvanishing at $s=0$ (`riemannZeta_zero`), the pole at $s=1$, `[NeZero N]`, principal/non-principal branching (`χ ≠ 1 ∨ s ≠ 1`), Euler factor nonvanishing for imprimitive characters ($\operatorname{Re}(s) > 0$), boundary behavior on $\operatorname{Re}(s) = 0, 1$, and critical-strip equivalence of Mathlib `0df444a3`'s `DirichletCharacter.LFunction`. `SmallClassNumbers.CorGKOf` is completely isolated outside the `MainTheorems` cone.
3. **Recommended Final Dynamic Kernel Certification**: Once the official `leanprover/lean4:v4.33.1` toolchain and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` cache are provisioned locally, run `lake build Main` and `#print axioms` on all 5 theorems to confirm dynamically that zero axioms appear outside the standard allowed set (`propext`, `Classical.choice`, `Quot.sound`).
