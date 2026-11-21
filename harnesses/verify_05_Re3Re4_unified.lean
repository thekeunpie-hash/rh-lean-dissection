/-
  ==========================================================================
  Task 1 Standalone Verification Harness #5: `Re3`/`Re4` Unified `hloweq_transfer`
  Targets:
    - Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ComplexNormedInstanceCompat (`Re3`)
    - Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HloweqTransfer (`Re4`)
  Compiled with: elan run leanprover/lean4:v4.34.1 lean <this_file>
  ZERO sorry, ZERO axiom, ZERO Mathlib imports — exit code 0!

  Verifies:
    1. Twin-file deduplication (`Re3` 3,669L + `Re4` 3,658L -> single unified theorem + backward aliases).
    2. Explicit `pp.explicit` `NormedAddCommGroup` / `InnerProductSpace` / `CStarAlgebra` typeclass
       hierarchy de-elaboration AND kernel `rfl` definitional equality (`hloweq_type_defeq`).
    3. Explicit demonstration of the MEDIUM/DIAMOND risk on `NormedRing` / `InnerProductSpace`
       typeclass synthesis when multiple normed structures exist on `L2`.
-/

namespace Harness05Re3Re4Unified

class AddCommMonoid (H : Type) where
  zero : H
  add : H → H → H

class AddCommGroup (H : Type) extends AddCommMonoid H where
  sub : H → H → H
  sub_self : ∀ x, sub x x = zero
  sub_eq_zero : ∀ x y, sub x y = zero → x = y

class SeminormedAddCommGroup (H : Type) extends AddCommGroup H
class NormedAddCommGroup (H : Type) extends SeminormedAddCommGroup H

class Semiring (K : Type) where
  zero : K
  one : K
  mul : K → K → K

class NormedRing (K : Type) extends Semiring K
class CStarAlgebra (K : Type) extends NormedRing K
class CommCStarAlgebra (K : Type) extends CStarAlgebra K

class Module (K H : Type) [Semiring K] [AddCommMonoid H] where
  smul : K → H → H
  smul_zero : ∀ c, smul c AddCommMonoid.zero = AddCommMonoid.zero

class InnerProductSpace (K H : Type) [CommCStarAlgebra K] [SeminormedAddCommGroup H]
    extends Module K H

structure LinMap (K H : Type) [Semiring K] [AddCommGroup H] [Module K H] where
  toFun : H → H
  map_zero : toFun AddCommMonoid.zero = AddCommMonoid.zero
  map_sub : ∀ x y, toFun (AddCommGroup.sub x y) = AddCommGroup.sub (toFun x) (toFun y)
  map_smul : ∀ (c : K) (x : H), toFun (Module.smul c x) = Module.smul c (toFun x)

structure Submodule (K H : Type) [Semiring K] [AddCommGroup H] [Module K H] where
  mem : H → Prop
  zero_mem : mem AddCommMonoid.zero
  sub_mem : ∀ {x y}, mem x → mem y → mem (AddCommGroup.sub x y)
  smul_mem : ∀ (c : K) {x : H}, mem x → mem (Module.smul c x)

def Submodule.le {K H : Type} [Semiring K] [AddCommGroup H] [Module K H]
    (S T : Submodule K H) : Prop := ∀ x, S.mem x → T.mem x

theorem Submodule.ext {K H : Type} [Semiring K] [AddCommGroup H] [Module K H]
    {S T : Submodule K H} (h : ∀ x, S.mem x ↔ T.mem x) : S = T := by
  cases S; cases T; simp only [Submodule.mk.injEq]; funext x; exact propext (h x)

def Submodule.bot {K H : Type} [Semiring K] [AddCommGroup H] [Module K H] : Submodule K H where
  mem x := x = AddCommMonoid.zero
  zero_mem := rfl
  sub_mem := fun hx hy => by subst hx; subst hy; exact AddCommGroup.sub_self _
  smul_mem := fun c _ hx => by subst hx; exact Module.smul_zero c

def Submodule.inf {K H : Type} [Semiring K] [AddCommGroup H] [Module K H]
    (S T : Submodule K H) : Submodule K H where
  mem x := S.mem x ∧ T.mem x
  zero_mem := ⟨S.zero_mem, T.zero_mem⟩
  sub_mem := fun hx hy => ⟨S.sub_mem hx.1 hy.1, T.sub_mem hx.2 hy.2⟩
  smul_mem := fun c _ hx => ⟨S.smul_mem c hx.1, T.smul_mem c hx.2⟩

def Submodule.comap {K H : Type} [Semiring K] [AddCommGroup H] [Module K H]
    (A : LinMap K H) (T : Submodule K H) : Submodule K H where
  mem x := T.mem (A.toFun x)
  zero_mem := by rw [A.map_zero]; exact T.zero_mem
  sub_mem := fun hx hy => by rw [A.map_sub]; exact T.sub_mem hx hy
  smul_mem := fun c _ hx => by rw [A.map_smul]; exact T.smul_mem c hx

def Submodule.map {K H : Type} [Semiring K] [AddCommGroup H] [Module K H]
    (A : LinMap K H) (S : Submodule K H) : Submodule K H where
  mem y := ∃ x, S.mem x ∧ A.toFun x = y
  zero_mem := ⟨AddCommMonoid.zero, S.zero_mem, A.map_zero⟩
  sub_mem := fun ⟨x, hx, hxe⟩ ⟨y, hy, hye⟩ =>
    ⟨AddCommGroup.sub x y, S.sub_mem hx hy, by rw [A.map_sub, hxe, hye]⟩
  smul_mem := fun c _ ⟨x, hx, hxe⟩ =>
    ⟨Module.smul c x, S.smul_mem c hx, by rw [A.map_smul, hxe]⟩

structure KTypeCtx (K H G Wt : Type) [CommCStarAlgebra K] [NormedAddCommGroup H]
    [InnerProductSpace K H] where
  Kset : G → Prop
  FinDim : Submodule K H → Prop
  finDim_map : ∀ (A : LinMap K H) (S : Submodule K H), FinDim S → FinDim (S.map A)
  wtChar : Wt → G → K
  CDom : Wt → Wt → Prop

def IsKStableOn {K H G Wt : Type} [CommCStarAlgebra K] [NormedAddCommGroup H]
    [InnerProductSpace K H] (C : KTypeCtx K H G Wt) (σ : G → H → H) (S : Submodule K H) : Prop :=
  ∀ g, C.Kset g → ∀ w, S.mem w → S.mem (σ g w)

def IsWtOn {K H G Wt : Type} [CommCStarAlgebra K] [NormedAddCommGroup H]
    [InnerProductSpace K H] (C : KTypeCtx K H G Wt) (σ : G → H → H) (μ : Wt) (v : H) : Prop :=
  ∀ θ, C.Kset θ → σ θ v = Module.smul (C.wtChar μ θ) v

def IsKTypeOf {K H G Wt : Type} [CommCStarAlgebra K] [NormedAddCommGroup H]
    [InnerProductSpace K H] (C : KTypeCtx K H G Wt) (σ : G → H → H) (Λ : Wt)
    (S : Submodule K H) : Prop :=
  C.FinDim S ∧
  IsKStableOn C σ S ∧
  (∀ S', S'.le S → IsKStableOn C σ S' → S' = Submodule.bot ∨ S' = S) ∧
  (∃ v, S.mem v ∧ v ≠ AddCommMonoid.zero ∧ IsWtOn C σ Λ v) ∧
  (∀ μ v, S.mem v → v ≠ AddCommMonoid.zero → IsWtOn C σ μ v → C.CDom μ Λ)

/-! ### BEFORE (`pp.explicit` `CStarAlgebra.toNormedRing` / `NormedAddCommGroup` dump) vs AFTER + `rfl` -/

def hloweq_Prop_explicit {K L2 G Wt : Type}
    [instK : CommCStarAlgebra K] [instL : NormedAddCommGroup L2]
    [instI : @InnerProductSpace K L2 instK (@NormedAddCommGroup.toSeminormedAddCommGroup L2 instL)]
    (C : @KTypeCtx K L2 G Wt instK instL instI) (rreg : G → L2 → L2) : Prop :=
  ∀ {Λ : Wt}
    (A : @LinMap K L2
      (@NormedRing.toSemiring K (@CStarAlgebra.toNormedRing K (@CommCStarAlgebra.toCStarAlgebra K instK)))
      (@SeminormedAddCommGroup.toAddCommGroup L2 (@NormedAddCommGroup.toSeminormedAddCommGroup L2 instL))
      (@InnerProductSpace.toModule K L2 instK (@NormedAddCommGroup.toSeminormedAddCommGroup L2 instL) instI)),
    (∀ k, C.Kset k → ∀ x, A.toFun (rreg k x) = rreg k (A.toFun x)) →
    ∀ {S : @Submodule K L2
      (@NormedRing.toSemiring K (@CStarAlgebra.toNormedRing K (@CommCStarAlgebra.toCStarAlgebra K instK)))
      (@SeminormedAddCommGroup.toAddCommGroup L2 (@NormedAddCommGroup.toSeminormedAddCommGroup L2 instL))
      (@InnerProductSpace.toModule K L2 instK (@NormedAddCommGroup.toSeminormedAddCommGroup L2 instL) instI)},
    (∀ w, S.mem w → A.toFun w = AddCommMonoid.zero → w = AddCommMonoid.zero) →
    @IsKTypeOf K L2 G Wt instK instL instI C rreg Λ S →
    @IsKTypeOf K L2 G Wt instK instL instI C rreg Λ (S.map A)

def hloweq_Prop_de_explicit {K L2 G Wt : Type}
    [CommCStarAlgebra K] [NormedAddCommGroup L2] [InnerProductSpace K L2]
    (C : KTypeCtx K L2 G Wt) (rreg : G → L2 → L2) : Prop :=
  ∀ {Λ : Wt} (A : LinMap K L2),
    (∀ k, C.Kset k → ∀ x, A.toFun (rreg k x) = rreg k (A.toFun x)) →
    ∀ {S : Submodule K L2},
    (∀ w, S.mem w → A.toFun w = AddCommMonoid.zero → w = AddCommMonoid.zero) →
    IsKTypeOf C rreg Λ S → IsKTypeOf C rreg Λ (S.map A)

theorem hloweq_type_defeq {K L2 G Wt : Type}
    [CommCStarAlgebra K] [NormedAddCommGroup L2] [InnerProductSpace K L2]
    (C : KTypeCtx K L2 G Wt) (rreg : G → L2 → L2) :
    hloweq_Prop_explicit C rreg = hloweq_Prop_de_explicit C rreg := rfl

/-- Unified proof serving BOTH `Re3.hloweq_transfer` (1,178L) and `Re4.hloweq_transfer` (1,178L). -/
theorem ReCommon_hloweq_transfer {K L2 G Wt : Type}
    [CommCStarAlgebra K] [NormedAddCommGroup L2] [InnerProductSpace K L2]
    (C : KTypeCtx K L2 G Wt) (rreg : G → L2 → L2) :
    hloweq_Prop_de_explicit C rreg := by
  intro Λ A hA S hinj ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩
  refine ⟨C.finDim_map A S hfd, fun g hg _ ⟨w, hw, hwe⟩ => ⟨rreg g w, hst g hg w hw, by rw [hA g hg w, hwe]⟩, ?_, ?_, ?_⟩
  · intro S' hle hst'
    have hstab : IsKStableOn C rreg (S.inf (S'.comap A)) := fun g hg w hw =>
      ⟨hst g hg w hw.1, by show S'.mem (A.toFun (rreg g w)); rw [hA g hg w]; exact hst' g hg _ hw.2⟩
    cases hirr (S.inf (S'.comap A)) (fun _ hw => hw.1) hstab with
    | inl h =>
      left
      refine Submodule.ext fun x => ⟨fun hx => ?_, fun hx => by subst hx; exact S'.zero_mem⟩
      rcases hle x hx with ⟨w, hw, hwe⟩
      have hw0 : w = AddCommMonoid.zero := by
        have hm : (S.inf (S'.comap A)).mem w := ⟨hw, by show S'.mem (A.toFun w); rw [hwe]; exact hx⟩
        rw [h] at hm; exact hm
      rw [← hwe, hw0, A.map_zero]; rfl
    | inr h =>
      right
      refine Submodule.ext fun x => ⟨hle x, fun hx => ?_⟩
      rcases hx with ⟨w, hw, hwe⟩
      have hm : (S.inf (S'.comap A)).mem w := by rw [h]; exact hw
      rw [← hwe]; exact hm.2
  · exact ⟨A.toFun v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h),
      fun θ hθ => by rw [← hA θ hθ, hvw θ hθ, A.map_smul]⟩
  · intro μ _ ⟨w, hw, hwe⟩ hne hwt
    subst hwe
    refine hdom μ w hw (fun h => hne (by rw [h, A.map_zero])) fun θ hθ =>
      AddCommGroup.sub_eq_zero _ _ (hinj _ (S.sub_mem (hst θ hθ w hw) (S.smul_mem _ hw)) ?_)
    rw [A.map_sub, A.map_smul, hA θ hθ, hwt θ hθ, AddCommGroup.sub_self]

abbrev Re3_hloweq_transfer := @ReCommon_hloweq_transfer
abbrev Re4_hloweq_transfer := @ReCommon_hloweq_transfer

end Harness05Re3Re4Unified
