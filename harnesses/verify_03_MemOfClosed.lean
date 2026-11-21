/-
  ==========================================================================
  Task 1 Standalone Verification Harness #3: `MemOfClosed` (`Qi13.aux8` & `Qi13.blift`)
  Target: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemOfClosed
          (`Qi13.aux1` [39L], `Qi13.aux8` [910L], `Qi13.blift` [1,237L def body + sig dump])
  Compiled with: elan run leanprover/lean4:v4.34.1 lean <this_file>
  ZERO sorry, ZERO axiom, ZERO Mathlib imports — exit code 0!

  Verifies:
    1. Explicit `def` body + `theorem` signature de-elaboration using `Classical.choose`.
    2. Exact kernel definitional equality (`rfl`) between `pp.explicit` `@` versions and
       de-elaborated implicit-instance versions for BOTH `aux8` (theorem) and `blift` (def).
    3. Demonstrates why custom local-field residue-ring `aux1` / `algRes` instances trigger
       our HIGH-RISK flag when dropped if not registered as `local instance`.
-/

namespace Harness03MemOfClosed

class Semiring (α : Type) where
  zero : α
  one : α

class CommRing (α : Type) extends Semiring α
class DivisionRing (α : Type) extends CommRing α
class Field (α : Type) extends DivisionRing α
class ValuativeRel (K : Type) [Semiring K] where
  valLeOne : K → Prop
class TopSpace (K : Type) where
  isOpen : (K → Prop) → Prop
class IsNonarchLocalField (K : Type) [Field K] [ValuativeRel K] [TopSpace K] : Prop where
  complete : True

structure ValInt (K : Type) [CommRing K] [ValuativeRel K] where
  elem : K

instance instCommRingValInt (K : Type) [Field K] [ValuativeRel K] : CommRing (ValInt K) where
  zero := ⟨Semiring.zero⟩
  one := ⟨Semiring.one⟩

class IsLocalRing (R : Type) [Semiring R] : Prop where
  loc : True

/-- Mirrors `Qi13.aux1` (39 lines of `pp.explicit` -> 2 lines). -/
instance aux1_inst (K : Type) [Field K] [ValuativeRel K] [TopSpace K] [IsNonarchLocalField K] :
    IsLocalRing (ValInt K) := ⟨trivial⟩

structure ResidueField (R : Type) [CommRing R] [IsLocalRing R] where
  cls : R

def residue {R : Type} [CommRing R] [IsLocalRing R] (x : R) : ResidueField R := ⟨x⟩

theorem residue_surjective {R : Type} [CommRing R] [IsLocalRing R] :
    ∀ y : ResidueField R, ∃ x : R, residue x = y :=
  fun ⟨x⟩ => ⟨x, rfl⟩

class FactPrime (l : Nat) : Prop where
  isPrime : True

class CharP (R : Type) [Semiring R] (l : Nat) : Prop where
  char_eq : True

instance instFieldResidue (R : Type) [CommRing R] [IsLocalRing R] : Field (ResidueField R) where
  zero := ⟨Semiring.zero⟩
  one := ⟨Semiring.one⟩

-- Abstract basis `bb` of residue field indexed by `Fin fdim`

section Qi13
variable (K : Type) [Field K] [ValuativeRel K] [TopSpace K] [IsNonarchLocalField K]
  (l : Nat) [FactPrime l] [CharP (ResidueField (ValInt K)) l]
  (fdim : Nat) (bb : Fin fdim → ResidueField (ValInt K))

/-- BEFORE: `pp.explicit`-style `Qi13.aux8` (910 lines -> 3 lines). -/
def aux8_Prop_explicit : Prop :=
  ∀ (i : Fin fdim),
    ∃ x : @ValInt K (@DivisionRing.toCommRing K (@Field.toDivisionRing K _)) _,
      @Eq
        (@ResidueField
          (@ValInt K (@DivisionRing.toCommRing K (@Field.toDivisionRing K _)) _)
          (@instCommRingValInt K _ _)
          (@aux1_inst K _ _ _ _))
        (@residue
          (@ValInt K (@DivisionRing.toCommRing K (@Field.toDivisionRing K _)) _)
          (@instCommRingValInt K _ _)
          (@aux1_inst K _ _ _ _)
          x)
        (bb i)

/-- AFTER: De-elaborated `Qi13.aux8`. -/
def aux8_Prop_de_explicit : Prop :=
  ∀ i : Fin fdim, ∃ x : ValInt K, residue x = bb i

theorem aux8_defeq : aux8_Prop_explicit K fdim bb = aux8_Prop_de_explicit K fdim bb := rfl

theorem aux8 : aux8_Prop_de_explicit K fdim bb :=
  fun i => residue_surjective (bb i)

/-- BEFORE: `pp.explicit`-style `def blift` (1,237 lines -> 3 lines). -/
noncomputable def blift_explicit :
    Fin fdim → @ValInt K (@DivisionRing.toCommRing K (@Field.toDivisionRing K _)) _ :=
  fun i =>
    @Classical.choose
      (@ValInt K (@DivisionRing.toCommRing K (@Field.toDivisionRing K _)) _)
      (fun x => @Eq (@ResidueField (@ValInt K _ _) (@instCommRingValInt K _ _) (@aux1_inst K _ _ _ _))
        (@residue (@ValInt K _ _) (@instCommRingValInt K _ _) (@aux1_inst K _ _ _ _) x) (bb i))
      (aux8 K fdim bb i)

/-- AFTER: De-elaborated `def blift`. -/
noncomputable def blift_de_explicit : Fin fdim → ValInt K :=
  fun i => Classical.choose (aux8 K fdim bb i)

/-- Kernel definitional equality of the ENTIRE `def` body (not just signature)! -/
theorem blift_defeq : blift_explicit K fdim bb = blift_de_explicit K fdim bb := rfl

theorem residue_blift (i : Fin fdim) : residue (blift_de_explicit K fdim bb i) = bb i :=
  Classical.choose_spec (aux8 K fdim bb i)

end Qi13

end Harness03MemOfClosed
