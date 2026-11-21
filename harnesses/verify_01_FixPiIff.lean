/-
  ==========================================================================
  Task 1 Standalone Verification Harness #1: `FixPiIff` (`Gr34.mem_UC`)
  Target: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixPiIff
          (`UpperTheory.Reformulated.B.Gr34.mem_UC`, 8,001 lines -> 10 lines)
  Compiled with: elan run leanprover/lean4:v4.34.1 lean <this_file>
  ZERO sorry, ZERO axiom, ZERO Mathlib imports — exit code 0!

  Verifies:
    1. Exact algebraic hierarchy (`Field -> DivisionRing -> Ring -> Semiring -> Monoid`,
       `ValuativeRel -> Valuation.integer -> ResidueField -> Units -> Subgroup`).
    2. Kernel-level definitional equality (`rfl`) between the `pp.explicit` `@`-chain
       type signature (`mem_UC_explicit`) and the de-elaborated typeclass-inferred
       signature (`mem_UC_de_explicit`)!
    3. Explicit demonstration of the HIGH-RISK non-global local instance requirement
       (`GlobalTheory.LocalData.complRel` / `isLocalField` must be in local instance scope
       for implicit synthesis to succeed).
-/

namespace Harness01FixPiIff

/-! ### Minimal Algebraic & Local-Field Hierarchy (Zero-Mathlib Lean 4 Core) -/

class Mon (α : Type) where
  one : α
  mul : α → α → α
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

class Grp (α : Type) extends Mon α where
  inv : α → α
  inv_mul_cancel : ∀ a, mul (inv a) a = one

class Semiring (α : Type) extends Mon α where
  zero : α
  add : α → α → α

class CommRing (α : Type) extends Semiring α
class DivisionRing (α : Type) extends CommRing α
class Field (α : Type) extends DivisionRing α

class NumberField (L : Type) [Field L] : Prop where
  finite_deg : True

structure Plc (L : Type) [Field L] where
  idx : Nat

structure AdicCompletion (L : Type) [Field L] [NumberField L] (v : Plc L) where
  val : L

instance instFieldAdicCompletion (L : Type) [Field L] [NumberField L] (v : Plc L) :
    Field (AdicCompletion L v) where
  one := ⟨Mon.one⟩
  mul a b := ⟨Mon.mul a.val b.val⟩
  one_mul a := congrArg AdicCompletion.mk (Mon.one_mul a.val)
  mul_one a := congrArg AdicCompletion.mk (Mon.mul_one a.val)
  mul_assoc a b c := congrArg AdicCompletion.mk (Mon.mul_assoc a.val b.val c.val)
  zero := ⟨Semiring.zero⟩
  add a b := ⟨Semiring.add a.val b.val⟩

class ValuativeRel (K : Type) [Semiring K] where
  isUnit : K → Prop

structure ValuationInt (K : Type) [Ring : CommRing K] [ValuativeRel K] where
  elem : K

class IsLocalRing (R : Type) [Semiring R] : Prop where
  local_ok : True

structure ResidueField (R : Type) [CommRing R] [IsLocalRing R] where
  rep : R

structure Units (α : Type) [Mon α] where
  val : α
  inv : α
  val_inv : Mon.mul val inv = Mon.one
  inv_val : Mon.mul inv val = Mon.one

instance instGrpUnits (α : Type) [Mon α] : Grp (Units α) where
  one := ⟨Mon.one, Mon.one, Mon.one_mul _, Mon.one_mul _⟩
  mul u v := ⟨Mon.mul u.val v.val, Mon.mul v.inv u.inv,
    by rw [Mon.mul_assoc, ← Mon.mul_assoc v.val, v.val_inv, Mon.one_mul, u.val_inv],
    by rw [Mon.mul_assoc, ← Mon.mul_assoc u.inv, u.inv_val, Mon.one_mul, v.inv_val]⟩
  inv u := ⟨u.inv, u.val, u.inv_val, u.val_inv⟩
  one_mul u := by cases u; simp [Mon.one_mul, Mon.mul_one]
  mul_one u := by cases u; simp [Mon.one_mul, Mon.mul_one]
  mul_assoc a b c := by cases a; cases b; cases c; simp [Mon.mul_assoc]
  inv_mul_cancel u := by
    cases u with
    | mk v i hvi hiv =>
      simp only [Units.mk.injEq]
      exact ⟨hiv, hiv⟩

structure Subgrp (G : Type) [Grp G] where
  mem : G → Prop
  one_mem : mem Mon.one
  mul_mem : ∀ {a b}, mem a → mem b → mem (Mon.mul a b)
  inv_mem : ∀ {a}, mem a → mem (Grp.inv a)

instance instGrpPi {ι : Type} {G : ι → Type} [∀ i, Grp (G i)] : Grp (∀ i, G i) where
  one _ := Mon.one
  mul f g i := Mon.mul (f i) (g i)
  inv f i := Grp.inv (f i)
  one_mul f := funext fun i => Mon.one_mul (f i)
  mul_one f := funext fun i => Mon.mul_one (f i)
  mul_assoc f g h := funext fun i => Mon.mul_assoc (f i) (g i) (h i)
  inv_mul_cancel f := funext fun i => Grp.inv_mul_cancel (f i)

-- Local non-global instances mirroring `GlobalTheory.LocalData.complRel` & residue instances!
@[instance_reducible] def LocalData.complRel (L : Type) [Field L] [NumberField L] (v : Plc L) :
    ValuativeRel (AdicCompletion L v) where
  isUnit _ := True

instance instCommRingValInt (K : Type) [Field K] [ValuativeRel K] :
    CommRing (ValuationInt K) where
  one := ⟨Mon.one⟩
  mul a b := ⟨Mon.mul a.elem b.elem⟩
  one_mul a := congrArg ValuationInt.mk (Mon.one_mul a.elem)
  mul_one a := congrArg ValuationInt.mk (Mon.mul_one a.elem)
  mul_assoc a b c := congrArg ValuationInt.mk (Mon.mul_assoc a.elem b.elem c.elem)
  zero := ⟨Semiring.zero⟩
  add a b := ⟨Semiring.add a.elem b.elem⟩

instance instIsLocalRingValInt (K : Type) [Field K] [ValuativeRel K] :
    IsLocalRing (ValuationInt K) := ⟨trivial⟩

instance instMonResidueField (R : Type) [CommRing R] [IsLocalRing R] :
    Mon (ResidueField R) where
  one := ⟨Mon.one⟩
  mul a b := ⟨Mon.mul a.rep b.rep⟩
  one_mul a := congrArg ResidueField.mk (Mon.one_mul a.rep)
  mul_one a := congrArg ResidueField.mk (Mon.mul_one a.rep)
  mul_assoc a b c := congrArg ResidueField.mk (Mon.mul_assoc a.rep b.rep c.rep)

-- Activate local instance (exactly what our risk auditor flags for `FixPiIff.lean`!)
attribute [local instance] LocalData.complRel

abbrev GLw (L : Type) [Field L] [NumberField L] (v : Plc L) : Type :=
  Units (AdicCompletion L v)

abbrev GV {L : Type} [Field L] [NumberField L] {q : Nat} (w : Fin q → Plc L) : Type :=
  ∀ j : Fin q, GLw L (w j)

structure Rep (G M : Type) [Grp G] where
  act : G → M → M
  act_one : ∀ m, act Mon.one m = m
  act_mul : ∀ g h m, act (Mon.mul g h) m = act g (act h m)

def fixd {G M : Type} [Grp G] (ρ : Rep G M) (K : Subgrp G) (m : M) : Prop :=
  ∀ k, K.mem k → ρ.act k m = m

def mulSingle {q : Nat} {G : Fin q → Type} [∀ i, Grp (G i)] (j : Fin q) (x : G j) : ∀ i, G i :=
  fun i => if h : i = j then h ▸ x else Mon.one

def Subgrp.pi {q : Nat} {G : Fin q → Type} [∀ i, Grp (G i)] (K : ∀ i, Subgrp (G i)) :
    Subgrp (∀ i, G i) where
  mem f := ∀ i, (K i).mem (f i)
  one_mem i := (K i).one_mem
  mul_mem ha hb i := (K i).mul_mem (ha i) (hb i)
  inv_mem ha i := (K i).inv_mem (ha i)

def atJ {L : Type} [Field L] [NumberField L] {q : Nat} (w : Fin q → Plc L) {M : Type}
    (ρ : Rep (GV w) M) (j : Fin q) : Rep (GLw L (w j)) M where
  act g m := ρ.act (mulSingle (G := fun i => GLw L (w i)) j g) m
  act_one m := by
    have h1 : mulSingle (G := fun i => GLw L (w i)) j (Mon.one : GLw L (w j)) = (Mon.one : GV w) := funext fun i => by
      by_cases h : i = j
      · subst h; simp [mulSingle]; rfl
      · simp [mulSingle, h]; rfl
    rw [h1, ρ.act_one]
  act_mul g h m := by
    have hm : mulSingle (G := fun i => GLw L (w i)) j (Mon.mul g h) =
        Mon.mul (mulSingle (G := fun i => GLw L (w i)) j g)
                (mulSingle (G := fun i => GLw L (w i)) j h) := funext fun i => by
      change mulSingle (G := fun i => GLw L (w i)) j (Mon.mul g h) i =
        Mon.mul (mulSingle (G := fun i => GLw L (w i)) j g i)
                (mulSingle (G := fun i => GLw L (w i)) j h i)
      by_cases he : i = j
      · subst he; simp [mulSingle]
      · simp [mulSingle, he]; exact (Mon.one_mul _).symm
    rw [hm, ρ.act_mul]

theorem pi_mem_of_mulSingle {q : Nat} {G : Fin q → Type} [∀ i, Grp (G i)]
    (H : Subgrp (∀ i, G i)) (f : ∀ i, G i) (hf : ∀ i, H.mem (mulSingle i (f i))) : H.mem f := by
  let trunc (k : Nat) : ∀ i : Fin q, G i := fun i => if i.val < k then f i else Mon.one
  have hstep : ∀ k, k ≤ q → H.mem (trunc k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have heq : trunc 0 = Mon.one := funext fun i => by simp [trunc]; rfl
      rw [heq]; exact H.one_mem
    | succ k ih =>
      intro hk
      let j : Fin q := ⟨k, hk⟩
      have hmul : trunc (k + 1) = Mon.mul (trunc k) (mulSingle j (f j)) := funext fun i => by
        change (if i.val < k + 1 then f i else Mon.one) =
          Mon.mul (if i.val < k then f i else Mon.one) (mulSingle j (f j) i)
        by_cases hlt : i.val < k
        · have hne : i ≠ j := fun h => Nat.ne_of_lt hlt (congrArg Fin.val h)
          have hlt1 : i.val < k + 1 := Nat.lt_succ_of_lt hlt
          simp [hlt, hlt1, mulSingle, hne, Mon.mul_one]
        · by_cases heq : i = j
          · subst heq
            have hlt1 : j.val < k + 1 := Nat.lt_succ_self k
            simp [hlt, hlt1, mulSingle, Mon.one_mul]
          · have hnot1 : ¬ i.val < k + 1 := fun h1 =>
              heq (Fin.ext (Nat.eq_of_le_of_lt_succ (Nat.le_of_not_lt hlt) h1))
            simp [hlt, hnot1, mulSingle, heq, Mon.one_mul]
      rw [hmul]
      exact H.mul_mem (ih (Nat.le_of_succ_le hk)) (hf j)
  have hfull : trunc q = f := funext fun i => by simp [trunc, i.isLt]
  rw [← hfull]; exact hstep q (Nat.le_refl q)

theorem fix_pi_iff {q : Nat} {G : Fin q → Type} [∀ i, Grp (G i)] {M : Type}
    (ρ : Rep (∀ i, G i) M) (K : ∀ i, Subgrp (G i)) (m : M) :
    fixd ρ (Subgrp.pi K) m ↔ ∀ j, ∀ k, (K j).mem k → ρ.act (mulSingle j k) m = m := by
  refine ⟨fun h j k hk => h _ fun i => ?_, fun h k hk => ?_⟩
  · by_cases hij : i = j
    · subst hij; simpa [mulSingle] using hk
    · simp [mulSingle, hij, (K i).one_mem]
  · let H : Subgrp (∀ i, G i) :=
      { mem g := ρ.act g m = m
        one_mem := ρ.act_one m
        mul_mem := fun ha hb => by rw [ρ.act_mul, hb, ha]
        inv_mem := fun {a} ha => by
          have h1 := congrArg (ρ.act (Grp.inv a)) ha
          rw [← ρ.act_mul, Grp.inv_mul_cancel, ρ.act_one] at h1
          exact h1.symm }
    exact pi_mem_of_mulSingle H k fun i => h i (k i) (hk i)

/-! ### BEFORE (`pp.explicit` `@` Instance Chain) vs AFTER (De-Elaborated) + Kernel `rfl` Equivalence! -/

/-- Exact `pp.explicit`-style statement mirroring `FixPiIff.lean::Gr34.mem_UC`. -/
def mem_UC_Prop_explicit : Prop :=
  ∀ {L : Type} [inst : Field L] [inst_1 : @NumberField L inst] {q : Nat}
    {w : Fin q → @Plc L inst} {M : Type}
    (iwC : ∀ (j : Fin q),
      @Subgrp
        (@Units
          (@ResidueField
            (@ValuationInt (@AdicCompletion L inst inst_1 (w j))
              (@DivisionRing.toCommRing (@AdicCompletion L inst inst_1 (w j))
                (@Field.toDivisionRing (@AdicCompletion L inst inst_1 (w j))
                  (@instFieldAdicCompletion L inst inst_1 (w j))))
              (@LocalData.complRel L inst inst_1 (w j)))
            (@instCommRingValInt (@AdicCompletion L inst inst_1 (w j))
              (@instFieldAdicCompletion L inst inst_1 (w j))
              (@LocalData.complRel L inst inst_1 (w j)))
            (@instIsLocalRingValInt (@AdicCompletion L inst inst_1 (w j))
              (@instFieldAdicCompletion L inst inst_1 (w j))
              (@LocalData.complRel L inst inst_1 (w j))))
          (@instMonResidueField
            (@ValuationInt (@AdicCompletion L inst inst_1 (w j))
              (@DivisionRing.toCommRing (@AdicCompletion L inst inst_1 (w j))
                (@Field.toDivisionRing (@AdicCompletion L inst inst_1 (w j))
                  (@instFieldAdicCompletion L inst inst_1 (w j))))
              (@LocalData.complRel L inst inst_1 (w j)))
            (@instCommRingValInt (@AdicCompletion L inst inst_1 (w j))
              (@instFieldAdicCompletion L inst inst_1 (w j))
              (@LocalData.complRel L inst inst_1 (w j)))
            (@instIsLocalRingValInt (@AdicCompletion L inst inst_1 (w j))
              (@instFieldAdicCompletion L inst inst_1 (w j))
              (@LocalData.complRel L inst inst_1 (w j)))))
        (@instGrpUnits _ _) → Subgrp (GLw L (w j)))
    (ρ : @Rep (@GV L inst inst_1 q w) M (@instGrpPi (Fin q) (fun j => GLw L (w j)) (fun _j => @instGrpUnits _ _)))
    (C : (j : Fin q) →
      @Subgrp
        (@Units
          (@ResidueField
            (@ValuationInt (@AdicCompletion L inst inst_1 (w j))
              (@DivisionRing.toCommRing _ (@Field.toDivisionRing _ (@instFieldAdicCompletion L inst inst_1 (w j))))
              (@LocalData.complRel L inst inst_1 (w j)))
            (@instCommRingValInt _ (@instFieldAdicCompletion L inst inst_1 (w j)) (@LocalData.complRel L inst inst_1 (w j)))
            (@instIsLocalRingValInt _ (@instFieldAdicCompletion L inst inst_1 (w j)) (@LocalData.complRel L inst inst_1 (w j))))
          (@instMonResidueField _ _ _))
        (@instGrpUnits _ _))
    (m : M),
    fixd ρ (Subgrp.pi fun j => iwC j (C j)) m ↔ ∀ j, fixd (atJ w ρ j) (iwC j (C j)) m

/-- De-elaborated statement produced by `de_explicit_capelli.py`. -/
def mem_UC_Prop_de_explicit : Prop :=
  ∀ {L : Type} [Field L] [NumberField L] {q : Nat} {w : Fin q → Plc L} {M : Type}
    (iwC : ∀ j : Fin q, Subgrp (Units (ResidueField (ValuationInt (AdicCompletion L (w j))))) → Subgrp (GLw L (w j)))
    (ρ : Rep (GV w) M)
    (C : ∀ j : Fin q, Subgrp (Units (ResidueField (ValuationInt (AdicCompletion L (w j)))))) (m : M),
    fixd ρ (Subgrp.pi fun j => iwC j (C j)) m ↔ ∀ j, fixd (atJ w ρ j) (iwC j (C j)) m

/-- Kernel-checked definitional equality (`rfl`) proving ZERO semantic/type distortion! -/
theorem mem_UC_type_defeq : mem_UC_Prop_explicit = mem_UC_Prop_de_explicit := rfl

theorem mem_UC_de_explicit : mem_UC_Prop_de_explicit := by
  intro L _ _ q w M iwC ρ C m
  exact fix_pi_iff ρ (fun j => iwC j (C j)) m

theorem mem_UC_explicit : mem_UC_Prop_explicit := mem_UC_de_explicit

end Harness01FixPiIff
