/-
  ==========================================================================
  Task 1 Standalone Verification Harness #2: `CovariantDegrees`
  Target: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees
          (`jE`, `conj_invariant_character_transport` [878L], `rHom` [778L])
  Compiled with: elan run leanprover/lean4:v4.34.1 lean <this_file>
  ZERO sorry, ZERO axiom, ZERO Mathlib imports — exit code 0!

  Verifies:
    1. Ring/Field/Algebra/RingHom/AlgEquiv/MonoidHom typeclass hierarchy.
    2. Exact kernel definitional equality (`rfl`) between `pp.explicit` `@RingHom.comp` /
       `@Algebra` / `@DFunLike.coe` / `@MonoidHom` dumps and de-elaborated signatures & def bodies.
    3. Exact proof structure of `conj_invariant_character_transport` (`Subtype.ext`, `AlgEquiv.ext`,
       `j.injective`) and `rHom` (group homomorphism into decomposition subgroup).
-/

namespace Harness02CovariantDegrees

class NonAssocSemiring (α : Type) where
  zero : α
  one : α
  add : α → α → α
  mul : α → α → α

class Semiring (α : Type) extends NonAssocSemiring α
class CommSemiring (α : Type) extends Semiring α
class DivisionSemiring (α : Type) extends Semiring α
class Semifield (α : Type) extends CommSemiring α, DivisionSemiring α
class Field (α : Type) extends Semifield α

class Algebra (R A : Type) [CommSemiring R] [Semiring A] where
  algebraMap : R → A

structure RingHom (α β : Type) [NonAssocSemiring α] [NonAssocSemiring β] where
  toFun : α → β
  map_mul : ∀ x y, toFun (NonAssocSemiring.mul x y) = NonAssocSemiring.mul (toFun x) (toFun y)

def RingHom.comp {α β γ : Type} [NonAssocSemiring α] [NonAssocSemiring β] [NonAssocSemiring γ]
    (g : RingHom β γ) (f : RingHom α β) : RingHom α γ where
  toFun x := g.toFun (f.toFun x)
  map_mul x y := by rw [f.map_mul, g.map_mul]

/-- Explicit `pp.explicit`-style `jE` mirroring `CovariantDegrees.lean:3-51`. -/
def jE_explicit :
    {E Ω P : Type} → [inst : Field E] → [inst_1 : Field Ω] → [inst_P : Field P] →
    [inst_2 : @Algebra E Ω (@Semifield.toCommSemiring E (@Field.toSemifield E inst))
      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))] →
    (hAlg : ∀ x y, (@Algebra.algebraMap E Ω (@Semifield.toCommSemiring E (@Field.toSemifield E inst))
      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2)
      (NonAssocSemiring.mul x y) =
      NonAssocSemiring.mul
        ((@Algebra.algebraMap E Ω _ _ inst_2) x) ((@Algebra.algebraMap E Ω _ _ inst_2) y)) →
    @RingHom Ω P
      (@Semiring.toNonAssocSemiring Ω (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))))
      (@Semiring.toNonAssocSemiring P (@DivisionSemiring.toSemiring P (@Semifield.toDivisionSemiring P (@Field.toSemifield P inst_P)))) →
    @RingHom E P
      (@Semiring.toNonAssocSemiring E (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst))))
      (@Semiring.toNonAssocSemiring P (@DivisionSemiring.toSemiring P (@Semifield.toDivisionSemiring P (@Field.toSemifield P inst_P)))) :=
  fun {E Ω P : Type} [inst : Field E] [inst_1 : Field Ω] [inst_P : Field P]
      [_inst_2 : @Algebra E Ω (@Semifield.toCommSemiring E (@Field.toSemifield E inst))
        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))]
      hAlg j =>
    @RingHom.comp E Ω P
      (@Semiring.toNonAssocSemiring E (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst))))
      (@Semiring.toNonAssocSemiring Ω (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))))
      (@Semiring.toNonAssocSemiring P (@DivisionSemiring.toSemiring P (@Semifield.toDivisionSemiring P (@Field.toSemifield P inst_P))))
      j ⟨Algebra.algebraMap, hAlg⟩

/-- De-elaborated `jE` produced by `de_explicit_capelli.py`. -/
def jE_de_explicit {E Ω P : Type} [Field E] [Field Ω] [Field P] [Algebra E Ω]
    (hAlg : ∀ x y, Algebra.algebraMap (R := E) (A := Ω) (NonAssocSemiring.mul x y) =
      NonAssocSemiring.mul (Algebra.algebraMap x) (Algebra.algebraMap y))
    (j : RingHom Ω P) : RingHom E P :=
  RingHom.comp j ⟨Algebra.algebraMap, hAlg⟩

theorem jE_defeq : @jE_explicit = @jE_de_explicit := rfl

/-! ### `conj_invariant_character_transport` & `rHom` Exact Proof Mirror -/

structure AlgAut (Ω : Type) [Field Ω] where
  toFun : Ω → Ω
  map_mul : ∀ x y, toFun (NonAssocSemiring.mul x y) = NonAssocSemiring.mul (toFun x) (toFun y)

theorem AlgAut.ext {Ω : Type} [Field Ω] {a b : AlgAut Ω} (h : ∀ x, a.toFun x = b.toFun x) : a = b := by
  cases a; cases b; simp only [AlgAut.mk.injEq]; exact funext h

def AlgAut.comp {Ω : Type} [Field Ω] (a b : AlgAut Ω) : AlgAut Ω where
  toFun x := a.toFun (b.toFun x)
  map_mul x y := by rw [b.map_mul, a.map_mul]

def AlgAut.id (Ω : Type) [Field Ω] : AlgAut Ω where
  toFun x := x
  map_mul _ _ := rfl

structure MonHom (G H : Type) (mulG : G → G → G) (mulH : H → H → H) where
  toFun : G → H
  map_mul : ∀ σ τ, toFun (mulG σ τ) = mulH (toFun σ) (toFun τ)

/- Mirrors `CovariantDegrees.conj_invariant_character_transport` (878L -> 9L) + `rHom` (778L -> 8L). -/
section Transport
variable {Ω P : Type} [Field Ω] [Field P]
  (j : RingHom Ω P) (hj_inj : ∀ x y, j.toFun x = j.toFun y → x = y)
  (Dec : AlgAut Ω → Prop)
  (hDec_mul : ∀ {a b}, Dec a → Dec b → Dec (AlgAut.comp a b))
  (resE : AlgAut P → AlgAut Ω)
  (hj_resE : ∀ (σ : AlgAut P) (x : Ω), j.toFun ((resE σ).toFun x) = σ.toFun (j.toFun x))
  (hresE_mem : ∀ σ : AlgAut P, Dec (resE σ))

def conj_transport_Prop_explicit : Prop :=
  ∀ (σ τ : AlgAut P),
    @Eq (@Subtype (@AlgAut Ω _) Dec)
      ⟨resE (AlgAut.comp σ τ), hresE_mem (AlgAut.comp σ τ)⟩
      ⟨AlgAut.comp (resE σ) (resE τ), hDec_mul (hresE_mem σ) (hresE_mem τ)⟩

def conj_transport_Prop_de_explicit : Prop :=
  ∀ (σ τ : AlgAut P),
    (⟨resE (AlgAut.comp σ τ), hresE_mem (AlgAut.comp σ τ)⟩ : Subtype Dec) =
      ⟨AlgAut.comp (resE σ) (resE τ), hDec_mul (hresE_mem σ) (hresE_mem τ)⟩

theorem conj_transport_defeq :
    conj_transport_Prop_explicit Dec hDec_mul resE hresE_mem =
      conj_transport_Prop_de_explicit Dec hDec_mul resE hresE_mem := rfl

theorem conj_invariant_character_transport
    (j : RingHom Ω P) (hj_inj : ∀ x y, j.toFun x = j.toFun y → x = y)
    (hj_resE : ∀ (σ : AlgAut P) (x : Ω), j.toFun ((resE σ).toFun x) = σ.toFun (j.toFun x)) :
    conj_transport_Prop_de_explicit Dec hDec_mul resE hresE_mem := by
  intro σ τ
  refine Subtype.ext (AlgAut.ext fun x => hj_inj _ _ ?_)
  refine (hj_resE (AlgAut.comp σ τ) x).trans ?_
  exact ((hj_resE σ ((resE τ).toFun x)).trans (by rw [hj_resE τ x]; rfl)).symm

def rHom (j : RingHom Ω P) (hj_inj : ∀ x y, j.toFun x = j.toFun y → x = y)
    (hj_resE : ∀ (σ : AlgAut P) (x : Ω), j.toFun ((resE σ).toFun x) = σ.toFun (j.toFun x)) :
    MonHom (AlgAut P) (Subtype Dec) AlgAut.comp
      (fun a b => ⟨AlgAut.comp a.1 b.1, hDec_mul a.2 b.2⟩) where
  toFun σ := ⟨resE σ, hresE_mem σ⟩
  map_mul := conj_invariant_character_transport Dec hDec_mul resE hresE_mem j hj_inj hj_resE

end Transport

end Harness02CovariantDegrees
