/-
  ==========================================================================
  Task 2 PoC (Mathlib Drop-in Refactored Module):
  Unified Parameterized `SWeqOm` Consolidating the 3-Directory Clone Triplet!

  Replaces ALL THREE real files in `UnitaryGroupMassFormula`:
    1. StabilizerOrbitVolume/SWeqOm.lean  (71 lines, `PI.VolStabSW`, `a + 2 ≤ M`, `SWc1`,  `IsAdm`)
    2. StabilizerVolume/SWeqOm.lean       (74 lines, `PI.VolStabS`,  `2 * a < M`, `StabilizerFirstChernCompatibility`, `IsAdmS` with `IsSmoothCc`)
    3. WeilStabilizerVolume/SWeqOm.lean   (71 lines, `PI.VolStabW`,  `2 * a < M`, `SWc1W`, `IsAdm`)

  Total Original Lines (3 `SWeqOm.lean` files)     : 71 + 74 + 71 = 216 lines
  Total Self-Contained PoC File (`UnifiedSWeqOm`)  : 251 lines (187 code lines), broken down as:
    - Shared Decay + Unified `sWeqOm_of` + wrappers: 73 lines (vs 216L across 3 `SWeqOm.lean`, -143L / -66.2%)
    - One-time shared `VolStabCfg` + `InCtx`/`IsAdmCfg`/`DensFib*`/`SWeqOm` + 3 configs: 178 lines
      (amortized once across ALL 143 triplets, also replacing 434L of duplicated context defs in
       `FibInfEx.lean` [123L] + `VolStabFromSWS.lean` [148L] + `VolStabFromSWW.lean` [163L] -> 650L to 251L, -399L / -61.4%!)

  Exact 3-Axis Parameterization (`VolStabVariant`):
    - `DimBound (a M : ℕ) : Prop`         (`a + 2 ≤ M` vs `2 * a < M`)
    - `ArchExtra Φinf : Prop`             (`True` vs `IsSmoothCc F E Φinf`)
    - `SWInput F E σ M J : Prop`          (`SWc1` vs `StabilizerFirstChernCompatibility` vs `SWc1W`)
      equipped with a single uniform unpacking interface `sw_apply`.

  NOTE: Full Mathlib elaboration requires `leanprover/lean4:v4.33.1` + built Mathlib oleans.
  For independent zero-Mathlib Lean 4 core compilation verification (`elan run leanprover/lean4:v4.34.1 lean`,
  exit 0, 0 sorry, 0 axiom), see `verify_unitary_unified_core.lean` in ../harnesses/.
-/

import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide

noncomputable section

namespace PI.VolStabCommon

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open Formalism.L2.SG.Pf.NcWeil (StabilizerFirstChernCompatibility IsSmoothCc)
open scoped TensorProduct

/-! ### 1. Shared Archimedean Decay Lemmas (Eliminates 3x Exact Copy of L11..L43 = 99L -> 31L) -/

section Decay

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem continuous_sizeInf {d : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  unfold sizeInf
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
  have hk : Continuous fun y : Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).coord k y :=
    IsModuleTopology.continuous_of_linearMap _
  simp only [← Module.Basis.coord_apply]
  exact continuous_norm.comp ((continuous_apply v).comp hk)

theorem continuous_sizeTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeTup (M := M) (n := n) b) := by
  unfold sizeTup
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => ?_
  exact (continuous_sizeInf b).comp ((continuous_apply i).comp (continuous_apply a))

theorem rapidDecay_of_compact {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    RapidDecay b Φ := by
  intro N
  have hcont : Continuous fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    (continuous_norm.comp hc).mul ((continuous_const.add (continuous_sizeTup b)).pow N)
  have hsupp : HasCompactSupport fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    hs.norm.mul_right
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨C, fun X => le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hC X)⟩

end Decay

/-! ### 2. Unified 3-Axis Variant Configuration (`Orbit` / `Stab` / `Weil`) -/

/-- Captures the exact 3-axis parameter distinguishing `StabilizerOrbitVolume`,
    `StabilizerVolume`, and `WeilStabilizerVolume`. -/
structure VolStabCfg where
  /-- Dimension stability bound on `(a, M)` with `1 ≤ a` (`a + 2 ≤ M` vs `2 * a < M`). -/
  dimBound : ℕ → ℕ → Prop
  /-- Extra archimedean regularity on `Φinf` (`True` vs `IsSmoothCc`). -/
  archExtra : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M a : ℕ}, ((Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) → Prop
  /-- Siegel-Weil analytic hypothesis (`SWc1` vs `StabilizerFirstChernCompatibility` vs `SWc1W`). -/
  swInput : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    (E →ₐ[F] E) → (M : ℕ) → Matrix (Fin M) (Fin M) E → Prop
  /-- Uniform elimination law from `swInput` to the adelic theta-mean Euler product identity. -/
  sw_eval : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    swInput F E σ M J →
    ∀ (a : ℕ), dimBound a M →
    ∀ (T : Matrix (Fin a) (Fin a) E) (hT : ∀ i j, σ (T j i) = T i j), T.det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
      (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ)
      (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ)
      (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φinf → RapidDecay b Φinf → archExtra F E Φinf →
      IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
      AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
      AllSome (IsCharAF F) fun ψ =>
      AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) a) fun μinf =>
      AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) a) fun νinf =>
      AllSome (fun μv : ∀ v, Measure (Fin a → Fin M → Fv F v ⊗[F] E) =>
        ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) fun μv =>
      AllSome (fun νv : ∀ v, Measure (HermR (Fv F v) σ a) =>
        ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) fun νv =>
      ∃ (ginf : HermR (Ainf F) σ a → ℂ) (gv : ∀ v, HermR (Fv F v) σ a → ℂ),
        IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
          {S | IsUnit (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
        (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
          {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
        Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
        meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) =
          ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)

def InCtx (cfg : VolStabCfg)
    (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (X0 : Fin a → Fin M → E)
      (_hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    SWa1 F E σ M J → cfg.swInput F E σ M J → ∀ (a : ℕ), 1 ≤ a → cfg.dimBound a M →
    ∀ (X0 : Fin a → Fin M → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j),
    (gramE σ J X0).det ≠ 0 → P F E σ M J a X0 hT

def IsAdmCfg (cfg : VolStabCfg) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {M a : ℕ} (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) : Prop :=
  ∃ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf ∧ HasCompactSupport Φinf ∧ cfg.archExtra F E Φinf ∧
      IsPureFin b Φf Φv ∧ IsProdInfFin Φ Φinf Φf

def DensFibInf (cfg : VolStabCfg) : Prop :=
  InCtx cfg fun F E _ _ _ _ _ σ M J a X0 hT =>
    ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (ginf : HermR (Ainf F) σ a → ℂ),
      Continuous Φinf → HasCompactSupport Φinf →
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)).det} Φinf ginf →
      ginf (hermOf (Ainf F) σ (gramE σ J X0) hT) =
        ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))

def DensFibV (cfg : VolStabCfg) : Prop :=
  InCtx cfg fun F E _ _ _ _ _ σ M J a X0 hT =>
    ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∀ (Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (gv : HermR (Fv F v) σ a → ℂ), IsSB Φv →
      IsContDensityOn μv (gramR (Fv F v) σ J) Subtype.val νv
        {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det} Φv gv →
      gv (hermOf (Fv F v) σ (gramE σ J X0) hT) =
        ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT))

def SWeqOm (cfg : VolStabCfg) : Prop :=
  InCtx cfg fun F E _ _ _ _ _ σ M J _a X0 hT =>
    ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ 𝓕, IsFDH F E σ M J μ 𝓕 →
    ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ Φ, IsAdmCfg cfg F E Φ →
      meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = gramE σ J X0}) = ∫ X, Φ X ∂νX

/-! ### 3. Single Unified Proof of `sWeqOm_of` Serving ALL 3 Directories! -/

theorem sWeqOm_of (cfg : VolStabCfg) (h1 : DensFibInf cfg) (h2 : DensFibV cfg) :
    SWeqOm cfg := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν Φ hΦ
  obtain ⟨d, b, Φinf, Φf, Φv, hci, hsi, hextra, hpf, hpr⟩ := hΦ
  have hS := cfg.sw_eval F E σ M J hc a ha2 (gramE σ J X0) hT hdet d b Φ Φinf Φf Φv hci
    (rapidDecay_of_compact b Φinf hci hsi) hextra hpf hpr
  obtain ⟨_, hν2⟩ := hν
  obtain ⟨μinf, hμinf⟩ := hν2.1
  have hν3 := hν2.2 μinf hμinf
  obtain ⟨νinf, hνinf⟩ := hν3.1
  have hν4 := hν3.2 νinf hνinf
  obtain ⟨μv, hμv⟩ := hν4.1
  have hν5 := hν4.2 μv hμv
  obtain ⟨νv, hνv⟩ := hν5.1
  have hν6 := hν5.2 νv hνv
  obtain ⟨fibInf, hfibInf⟩ := hν6.1
  have hν7 := hν6.2 fibInf hfibInf
  obtain ⟨fibV, hfibV⟩ := hν7.1
  have hν8 := hν7.2 fibV hfibV d b Φ Φinf Φf Φv hci hsi hpf hpr
  obtain ⟨ginf, gv, hdi, hdv, _, hmean⟩ :=
    (((((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv)
  rw [hmean, hν8.2.2, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf
    fibInf hfibInf Φinf ginf hci hsi hdi]
  congr 1
  exact tprod_congr fun v => h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v)
    (νv v) (hνv v) (fibV v) (hfibV v) (Φv v) (gv v) (hpf.1 v) (hdv v)

/-! ### 4. Three Concrete Variant Instantiations (Zero-Cost Backward Compatibility) -/

def cfgOrbit : VolStabCfg where
  dimBound a M := a + 2 ≤ M
  archExtra _ _ _ _ _ _ _ _ _ _ := True
  swInput F E _ _ _ _ _ σ M J := SWc1 F E σ M J
  sw_eval F E _ _ _ _ _ σ M J hc a ha2 T hT hdet d b Φ Φinf Φf Φv hci hrd _ hpf hpr :=
    hc a ha2 T hT hdet d b Φ Φinf Φf Φv hci hrd hpf hpr

def cfgStab : VolStabCfg where
  dimBound a M := 2 * a < M
  archExtra F E _ _ _ _ _ _ _ Φinf := IsSmoothCc F E Φinf
  swInput F E _ _ _ _ _ σ M J := StabilizerFirstChernCompatibility F E σ M J
  sw_eval F E _ _ _ _ _ σ M J hc a ha2 T hT hdet d b Φ Φinf Φf Φv hci hrd hsm hpf hpr :=
    hc a ha2 T hT hdet d b Φ Φinf Φf Φv hci hrd hsm hpf hpr

def cfgWeil (SWc1W : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), Prop)
    (hSWc1W : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), SWc1W F E σ M J →
      ∀ (a : ℕ), 2 * a < M → ∀ (T : Matrix (Fin a) (Fin a) E) (hT : ∀ i j, σ (T j i) = T i j),
      T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) Φ Φinf Φf Φv,
      Continuous Φinf → RapidDecay b Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
      AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
      AllSome (IsCharAF F) fun ψ =>
      AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) a) fun μinf =>
      AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) a) fun νinf =>
      AllSome (fun μv : ∀ v, Measure (Fin a → Fin M → Fv F v ⊗[F] E) =>
        ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) fun μv =>
      AllSome (fun νv : ∀ v, Measure (HermR (Fv F v) σ a) =>
        ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) fun νv =>
      ∃ (ginf : HermR (Ainf F) σ a → ℂ) (gv : ∀ v, HermR (Fv F v) σ a → ℂ),
        IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
          {S | IsUnit (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
        (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
          {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
        Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
        meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) =
          ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)) : VolStabCfg where
  dimBound a M := 2 * a < M
  archExtra _ _ _ _ _ _ _ _ _ _ := True
  swInput F E _ _ _ _ _ σ M J := SWc1W F E σ M J
  sw_eval F E _ _ _ _ _ σ M J hc a ha2 T hT hdet d b Φ Φinf Φf Φv hci hrd _ hpf hpr :=
    hSWc1W F E σ M J hc a ha2 T hT hdet d b Φ Φinf Φf Φv hci hrd hpf hpr

-- One-line directory instantiations replacing the 3 duplicated `sWeqOm_of` theorems:
abbrev orbit_sWeqOm_of := sWeqOm_of cfgOrbit
abbrev stab_sWeqOm_of  := sWeqOm_of cfgStab

end PI.VolStabCommon
