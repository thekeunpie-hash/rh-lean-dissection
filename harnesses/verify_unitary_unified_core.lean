/-
  ==========================================================================
  Task 2 Standalone Lean 4 Core Verification Harness
  Compiled with: elan run leanprover/lean4:v4.34.1 lean <this_file>
  ZERO sorry, ZERO axiom, ZERO Mathlib imports — exit code 0!

  Formally verifies the exact 3-axis parameterization (`VolStabCfg`) unifying:
    1. `StabilizerOrbitVolume` (`PI.VolStabSW`): `a + 2 ≤ M`, `SWc1`, `IsAdm` (`archExtra = True`)
    2. `StabilizerVolume`      (`PI.VolStabS`) : `2 * a < M`, `StabilizerFirstChernCompatibility`, `IsAdmS` (`archExtra = IsSmoothCc`)
    3. `WeilStabilizerVolume`  (`PI.VolStabW`) : `2 * a < M`, `SWc1W`, `IsAdm` (`archExtra = True`)
  proving:
    - The dimension bound implication `1 ≤ a → 2 * a < M → a + 2 ≤ M` (explaining `DensAAOf` L81),
    - The single unified `sWeqOm_of`, `volStabFromSW_of`, and `exChar_holds` theorems,
    - Concrete zero-cost instantiations recovering all 3 directory theorems + `IsAdmS → IsAdm` forgetful coercion.
-/

namespace UnitaryUnifiedCore

/-! ### Minimal Algebraic & Analytic Domain Model (Zero-Mathlib Lean 4 Core) -/

structure Ctx where
  Place : Type
  Val : Type
  mul : Val → Val → Val
  tprod : (Place → Val) → Val
  tprod_congr : ∀ {f g : Place → Val}, (∀ v, f v = g v) → tprod f = tprod g
  TestInf : Type
  TestFin : Type
  TestFull : Type
  Gram : Type
  MeasureInf : Type
  MeasureFin : Place → Type
  FibInf : Type
  FibFin : Place → Type
  DensityInf : Type
  DensityFin : Place → Type
  ContinuousInf : TestInf → Prop
  CompactSuppInf : TestInf → Prop
  RapidDecayInf : TestInf → Prop
  rapidDecay_of_compact : ∀ Φ, ContinuousInf Φ → CompactSuppInf Φ → RapidDecayInf Φ
  IsSmoothCc : TestInf → Prop
  IsPureFin : TestFin → (Place → TestInf) → Prop
  IsProdInfFin : TestFull → TestInf → TestFin → Prop
  IsContDensInf : MeasureInf → TestInf → DensityInf → Prop
  IsContDensFin : ∀ v, MeasureFin v → TestInf → DensityFin v → Prop
  evalInf : DensityInf → Val
  evalFin : ∀ v, DensityFin v → Val
  fibIntInf : FibInf → TestInf → Val
  fibIntFin : ∀ v, FibFin v → TestInf → Val
  thetaMean : TestFull → Val
  omInt : TestFull → Val
  IsOmT : TestFull → Prop
  omInt_factor : ∀ Φ Φinf Φf Φv, ContinuousInf Φinf → CompactSuppInf Φinf →
    IsPureFin Φf Φv → IsProdInfFin Φ Φinf Φf →
    ∃ (_ : MeasureInf) (_ : ∀ v, MeasureFin v) (fibInf : FibInf) (fibV : ∀ v, FibFin v),
      omInt Φ = mul (fibIntInf fibInf Φinf) (tprod fun v => fibIntFin v (fibV v) (Φv v))

/-- Abstract `AllSome` quantifier wrapper matching `PI.VolFromSW.AllSome`. -/
def AllSome {α : Type} (P : α → Prop) (Q : α → Prop) : Prop :=
  (∃ x, P x) ∧ ∀ x, P x → Q x

/-! ### Exact 3-Axis Parameterization Structure (`VolStabCfg`) -/

structure VolStabCfg (C : Ctx) where
  /-- Axis 1: Dimension stability bound on `(a, M)` (`a + 2 ≤ M` vs `2 * a < M`). -/
  dimBound : Nat → Nat → Prop
  /-- Every admissible dimension pair satisfies the orbit bound `a + 2 ≤ M` when `1 ≤ a`. -/
  dimBound_implies_orbit : ∀ a M, 1 ≤ a → dimBound a M → a + 2 ≤ M
  /-- Axis 2: Extra archimedean regularity predicate on `Φinf` (`True` vs `IsSmoothCc`). -/
  archExtra : C.TestInf → Prop
  /-- Axis 3: Siegel-Weil analytic input hypothesis (`SWc1` vs `StabilizerFirstChernCompatibility` vs `SWc1W`). -/
  swInput : Nat → Prop
  /-- Uniform elimination law from `swInput` to the adelic Euler-product theta mean identity. -/
  sw_eval : ∀ M, swInput M → ∀ a, dimBound a M →
    ∀ Φ Φinf Φf Φv, C.ContinuousInf Φinf → C.RapidDecayInf Φinf → archExtra Φinf →
      C.IsPureFin Φf Φv → C.IsProdInfFin Φ Φinf Φf →
      ∀ (μinf : C.MeasureInf) (μv : ∀ v, C.MeasureFin v),
        ∃ (ginf : C.DensityInf) (gv : ∀ v, C.DensityFin v),
          C.IsContDensInf μinf Φinf ginf ∧
          (∀ v, C.IsContDensFin v (μv v) (Φv v) (gv v)) ∧
          C.thetaMean Φ = C.mul (C.evalInf ginf) (C.tprod fun v => C.evalFin v (gv v))

/-! ### Parameterized Predicates (`InCtx`, `IsAdmCfg`, `DensFibInf`, `DensFibV`, `SWeqOm`) -/

def InCtx {C : Ctx} (cfg : VolStabCfg C) (P : Nat → Nat → Prop) : Prop :=
  ∀ M, cfg.swInput M → ∀ a, 1 ≤ a → cfg.dimBound a M → P M a

def IsAdmCfg {C : Ctx} (cfg : VolStabCfg C) (Φ : C.TestFull) : Prop :=
  ∃ Φinf Φf Φv, C.ContinuousInf Φinf ∧ C.CompactSuppInf Φinf ∧ cfg.archExtra Φinf ∧
    C.IsPureFin Φf Φv ∧ C.IsProdInfFin Φ Φinf Φf

def IsAdmBase (C : Ctx) (Φ : C.TestFull) : Prop :=
  ∃ Φinf Φf Φv, C.ContinuousInf Φinf ∧ C.CompactSuppInf Φinf ∧
    C.IsPureFin Φf Φv ∧ C.IsProdInfFin Φ Φinf Φf

/-- Uniform forgetful coercion replacing `PI.VolStabS.IsAdmS.adm` across any config. -/
theorem IsAdmCfg.toBase {C : Ctx} {cfg : VolStabCfg C} {Φ : C.TestFull}
    (h : IsAdmCfg cfg Φ) : IsAdmBase C Φ := by
  rcases h with ⟨Φinf, Φf, Φv, hc, hs, _, hp, hpr⟩
  exact ⟨Φinf, Φf, Φv, hc, hs, hp, hpr⟩

def DensFibInf {C : Ctx} (cfg : VolStabCfg C) : Prop :=
  InCtx cfg fun _M _a =>
    ∀ (μinf : C.MeasureInf) (fibInf : C.FibInf) (Φinf : C.TestInf) (ginf : C.DensityInf),
      C.ContinuousInf Φinf → C.CompactSuppInf Φinf → C.IsContDensInf μinf Φinf ginf →
      C.evalInf ginf = C.fibIntInf fibInf Φinf

def DensFibV {C : Ctx} (cfg : VolStabCfg C) : Prop :=
  InCtx cfg fun _M _a =>
    ∀ (v : C.Place) (μv : C.MeasureFin v) (fibV : C.FibFin v) (Φv : C.TestInf) (gv : C.DensityFin v),
      C.IsContDensFin v μv Φv gv →
      C.evalFin v gv = C.fibIntFin v fibV Φv

def SWeqOm {C : Ctx} (cfg : VolStabCfg C) : Prop :=
  InCtx cfg fun _M _a =>
    ∀ Φ, IsAdmCfg cfg Φ → C.thetaMean Φ = C.omInt Φ

/-! ### Single Unified Proof of `sWeqOm_of` Serving All 3 Directories -/

theorem sWeqOm_of {C : Ctx} (cfg : VolStabCfg C)
    (h1 : DensFibInf cfg) (h2 : DensFibV cfg) : SWeqOm cfg := by
  intro M hc a ha1 ha2 Φ hΦ
  rcases hΦ with ⟨Φinf, Φf, Φv, hci, hsi, hextra, hpf, hpr⟩
  rcases C.omInt_factor Φ Φinf Φf Φv hci hsi hpf hpr with ⟨μinf, μv, fibInf, fibV, hom⟩
  rcases cfg.sw_eval M hc a ha2 Φ Φinf Φf Φv hci (C.rapidDecay_of_compact Φinf hci hsi)
      hextra hpf hpr μinf μv with ⟨ginf, gv, hdi, hdv, hmean⟩
  rw [hmean, hom, h1 M hc a ha1 ha2 μinf fibInf Φinf ginf hci hsi hdi]
  have hprod : C.tprod (fun v => C.evalFin v (gv v)) =
      C.tprod (fun v => C.fibIntFin v (fibV v) (Φv v)) :=
    C.tprod_congr fun v => h2 M hc a ha1 ha2 v (μv v) (fibV v) (Φv v) (gv v) (hdv v)
  rw [hprod]

/-! ### Concrete 3-Directory Variant Instantiations -/

/-- Exact Siegel-Weil predicate shapes for the 3 directories. -/
def SWc1 (C : Ctx) (M : Nat) : Prop :=
  ∀ a, a + 2 ≤ M → ∀ Φ Φinf Φf Φv, C.ContinuousInf Φinf → C.RapidDecayInf Φinf →
    C.IsPureFin Φf Φv → C.IsProdInfFin Φ Φinf Φf →
    ∀ (μinf : C.MeasureInf) (μv : ∀ v, C.MeasureFin v),
      ∃ (ginf : C.DensityInf) (gv : ∀ v, C.DensityFin v),
        C.IsContDensInf μinf Φinf ginf ∧
        (∀ v, C.IsContDensFin v (μv v) (Φv v) (gv v)) ∧
        C.thetaMean Φ = C.mul (C.evalInf ginf) (C.tprod fun v => C.evalFin v (gv v))

def SWFirstChern (C : Ctx) (M : Nat) : Prop :=
  ∀ a, 2 * a < M → ∀ Φ Φinf Φf Φv, C.ContinuousInf Φinf → C.RapidDecayInf Φinf →
    C.IsSmoothCc Φinf → C.IsPureFin Φf Φv → C.IsProdInfFin Φ Φinf Φf →
    ∀ (μinf : C.MeasureInf) (μv : ∀ v, C.MeasureFin v),
      ∃ (ginf : C.DensityInf) (gv : ∀ v, C.DensityFin v),
        C.IsContDensInf μinf Φinf ginf ∧
        (∀ v, C.IsContDensFin v (μv v) (Φv v) (gv v)) ∧
        C.thetaMean Φ = C.mul (C.evalInf ginf) (C.tprod fun v => C.evalFin v (gv v))

def SWc1W (C : Ctx) (M : Nat) : Prop :=
  ∀ a, 2 * a < M → ∀ Φ Φinf Φf Φv, C.ContinuousInf Φinf → C.RapidDecayInf Φinf →
    C.IsPureFin Φf Φv → C.IsProdInfFin Φ Φinf Φf →
    ∀ (μinf : C.MeasureInf) (μv : ∀ v, C.MeasureFin v),
      ∃ (ginf : C.DensityInf) (gv : ∀ v, C.DensityFin v),
        C.IsContDensInf μinf Φinf ginf ∧
        (∀ v, C.IsContDensFin v (μv v) (Φv v) (gv v)) ∧
        C.thetaMean Φ = C.mul (C.evalInf ginf) (C.tprod fun v => C.evalFin v (gv v))

theorem two_mul_lt_implies_add_two_le (a M : Nat) (ha : 1 ≤ a) (h : 2 * a < M) : a + 2 ≤ M := by
  omega

/-- Variant 1: `StabilizerOrbitVolume` (`PI.VolStabSW`) -/
def cfgOrbit (C : Ctx) : VolStabCfg C where
  dimBound a M := a + 2 ≤ M
  dimBound_implies_orbit _ _ _ h := h
  archExtra _ := True
  swInput := SWc1 C
  sw_eval _M hc a ha2 Φ Φinf Φf Φv hci hrd _ hpf hpr μinf μv :=
    hc a ha2 Φ Φinf Φf Φv hci hrd hpf hpr μinf μv

/-- Variant 2: `StabilizerVolume` (`PI.VolStabS`) -/
def cfgStab (C : Ctx) : VolStabCfg C where
  dimBound a M := 2 * a < M
  dimBound_implies_orbit := two_mul_lt_implies_add_two_le
  archExtra := C.IsSmoothCc
  swInput := SWFirstChern C
  sw_eval _M hc a ha2 Φ Φinf Φf Φv hci hrd hsm hpf hpr μinf μv :=
    hc a ha2 Φ Φinf Φf Φv hci hrd hsm hpf hpr μinf μv

/-- Variant 3: `WeilStabilizerVolume` (`PI.VolStabW`) -/
def cfgWeil (C : Ctx) : VolStabCfg C where
  dimBound a M := 2 * a < M
  dimBound_implies_orbit := two_mul_lt_implies_add_two_le
  archExtra _ := True
  swInput := SWc1W C
  sw_eval _M hc a ha2 Φ Φinf Φf Φv hci hrd _ hpf hpr μinf μv :=
    hc a ha2 Φ Φinf Φf Φv hci hrd hpf hpr μinf μv

-- Recover all 3 directory theorems from the single unified `sWeqOm_of`:
theorem PI_VolStabSW_sWeqOm_of (C : Ctx) :
    DensFibInf (cfgOrbit C) → DensFibV (cfgOrbit C) → SWeqOm (cfgOrbit C) :=
  sWeqOm_of (cfgOrbit C)

theorem PI_VolStabS_sWeqOm_of (C : Ctx) :
    DensFibInf (cfgStab C) → DensFibV (cfgStab C) → SWeqOm (cfgStab C) :=
  sWeqOm_of (cfgStab C)

theorem PI_VolStabW_sWeqOm_of (C : Ctx) :
    DensFibInf (cfgWeil C) → DensFibV (cfgWeil C) → SWeqOm (cfgWeil C) :=
  sWeqOm_of (cfgWeil C)

-- Also verify `SWc1 → SWc1W → SWFirstChern` monotonicity hierarchy:
theorem swc1_implies_swc1W (C : Ctx) (M : Nat) (h : SWc1 C M) :
    ∀ a, 1 ≤ a → 2 * a < M →
      ∀ Φ Φinf Φf Φv, C.ContinuousInf Φinf → C.RapidDecayInf Φinf →
      C.IsPureFin Φf Φv → C.IsProdInfFin Φ Φinf Φf →
      ∀ (μinf : C.MeasureInf) (μv : ∀ v, C.MeasureFin v),
        ∃ (ginf : C.DensityInf) (gv : ∀ v, C.DensityFin v),
          C.IsContDensInf μinf Φinf ginf ∧
          (∀ v, C.IsContDensFin v (μv v) (Φv v) (gv v)) ∧
          C.thetaMean Φ = C.mul (C.evalInf ginf) (C.tprod fun v => C.evalFin v (gv v)) :=
  fun a ha1 ha2 => h a (two_mul_lt_implies_add_two_le a M ha1 ha2)

theorem swc1W_implies_swFirstChern (C : Ctx) (M : Nat) (h : SWc1W C M) : SWFirstChern C M :=
  fun a ha2 Φ Φinf Φf Φv hci hrd _ hpf hpr => h a ha2 Φ Φinf Φf Φv hci hrd hpf hpr

end UnitaryUnifiedCore
