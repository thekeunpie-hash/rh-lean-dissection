/-
  Refactored Mathlib Drop-In: `golfed_RingObjectsOfMatrixData.lean`
  Original: RingObjectsOfMatrixData.lean (588L; `ring_objects_of_matrix_data`: 479L body, 92 `have`, maxHeartbeats 8000000).
  Exact public statements preserved (`rank_block`, `eDiag'`, `ring_objects_of_matrix_data`), 0 `sorry`, 0 `axiom`.
  Standalone Lean 4.34.1 core verification: `harnesses/verify_RingObjectsOfMatrixData_core.lean` (exit 0).
-/

import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.FinrankRangeEq

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

/-! ### 1. Public Helper Theorems (Exact Original Signatures, Golfed Bodies) -/

theorem rank_block {K : Type*} [Field K] {d : Type} [Fintype d] [DecidableEq d] {α : Type} [DecidableEq α]
    (bl : d → α) (k : α) (M : Matrix d d K) (hM : ∀ a b, (bl a ≠ k ∨ bl b ≠ k) → M a b = 0) :
    (M.toSquareBlock bl k).rank = M.rank := by
  let P : Matrix {a // bl a = k} d K := Matrix.of fun i a => if (i : d) = a then (1 : K) else 0
  have h1 : M.toSquareBlock bl k = P * M * P.transpose := by
    ext i j; simp [P, Matrix.mul_apply, Matrix.toSquareBlock_def, Matrix.transpose_apply]
  have h2 : M = P.transpose * M.toSquareBlock bl k * P := by
    ext a b
    simp only [P, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.toSquareBlock_def]
    by_cases ha : bl a = k
    · by_cases hb : bl b = k
      · rw [Finset.sum_eq_single ⟨b, hb⟩]
        · rw [Finset.sum_eq_single ⟨a, ha⟩]
          · simp
          · intro i _ hi; simp [show (i : d) ≠ a from fun h => hi (Subtype.ext h)]
          · simp
        · intro j _ hj; simp [show (j : d) ≠ b from fun h => hj (Subtype.ext h)]
        · simp
      · rw [hM a b (Or.inr hb)]
        refine (Finset.sum_eq_zero fun j _ => ?_).symm
        simp [show (j : d) ≠ b from fun h => hb (h ▸ j.2)]
    · rw [hM a b (Or.inl ha)]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      refine mul_eq_zero_of_left (Finset.sum_eq_zero fun i _ => ?_) _
      simp [show (i : d) ≠ a from fun h => ha (h ▸ i.2)]
  exact le_antisymm
    (h1 ▸ (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))
    (h2 ▸ (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))

theorem eDiag' (A : Type) [CommRing A] (d : Type) [Fintype d] [DecidableEq d] (S : d → Prop)
    [DecidablePred S] (β : d → A) (t : ℕ) (α : ℕ → A) :
    (Matrix.diagonal fun a => if S a then (1 : A) else 0) * ((List.range t).tail.map fun i =>
      (Matrix.diagonal fun a => if S a then β a else 0) -
        α i • (Matrix.diagonal fun a => if S a then (1 : A) else 0)).prod =
      Matrix.diagonal fun a => if S a then ∏ i ∈ Finset.Ioo 0 t, (β a - α i) else 0 := by
  have hf : ∀ i, (Matrix.diagonal fun a => if S a then β a else 0) -
      α i • (Matrix.diagonal fun a => if S a then (1 : A) else 0) =
      Matrix.diagonal fun a => if S a then β a - α i else 0 := fun i => by
    ext a b
    by_cases hab : a = b
    · subst hab; by_cases hs : S a <;> simp [hs]
    · simp [Matrix.diagonal_apply, hab]
  have hp : ∀ l : List ℕ, (Matrix.diagonal fun a => if S a then (1 : A) else 0) *
      (l.map fun i => Matrix.diagonal fun a => if S a then β a - α i else 0).prod =
      Matrix.diagonal fun a => if S a then (l.map fun i => β a - α i).prod else 0 := by
    intro l
    induction l with
    | nil => simp only [List.map_nil, List.prod_nil, mul_one]
    | cons x l ih =>
      have hcomm : ∀ f g : d → A, Matrix.diagonal f * Matrix.diagonal g = Matrix.diagonal g * Matrix.diagonal f :=
        fun f g => by rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]; congr 1; funext a; exact mul_comm _ _
      rw [List.map_cons, List.prod_cons, ← mul_assoc, hcomm, mul_assoc, ih, Matrix.diagonal_mul_diagonal]
      congr 1; funext a; by_cases hs : S a <;> simp [hs]
  have hl : ∀ f : ℕ → A, ((List.range t).tail.map f).prod = ∏ i ∈ Finset.Ioo 0 t, f i := fun f => by
    rw [← List.prod_toFinset f (List.Nodup.sublist (List.tail_sublist _) (List.nodup_range ..))]
    congr 1; ext x; rw [List.mem_toFinset, Finset.mem_Ioo]
    cases t with
    | zero => simp
    | succ n =>
      rw [List.range_succ_eq_map, List.tail_cons, List.mem_map]
      exact ⟨fun ⟨y, hy, h⟩ => by rw [List.mem_range] at hy; omega,
        fun h => ⟨x - 1, List.mem_range.2 (by omega), by omega⟩⟩
  simp only [hf]; rw [hp]; congr 1; funext a; simp only [hl]

/-! ### 2. Extracted Cohesive Private Helper Lemmas (Isolated Contexts -> Eliminates Heartbeat Explosion) -/

private theorem map_diagonal_ite {A B d : Type*} [CommRing A] [CommRing B] [DecidableEq d]
    (f : A →+* B) (P : d → Prop) [DecidablePred P] (v : d → A) :
    (Matrix.diagonal fun a => if P a then v a else 0).map f =
      Matrix.diagonal fun a => if P a then f (v a) else 0 := by
  ext i j
  by_cases hij : i = j
  · subst hij; by_cases hi : P i <;> simp [hi]
  · simp [Matrix.diagonal_apply_ne _ hij]

private theorem block_subsingleton {d : Type} [Fintype d] {t : ℕ} {bl : d → Fin (t + 1)}
    (hc1 : ∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1)
    {k : Fin (t + 1)} (hk : k ≠ 0) : Subsingleton {a // bl a = k} :=
  Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 k hk))

private theorem block_nonempty {d : Type} [Fintype d] {t : ℕ} {bl : d → Fin (t + 1)}
    (hc1 : ∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1)
    {k : Fin (t + 1)} (hk : k ≠ 0) : Nonempty {a // bl a = k} :=
  Fintype.card_pos_iff.mp (by rw [hc1 k hk]; norm_num)

private theorem block_inj_of_ne_zero {d : Type} [Fintype d] {t : ℕ} {bl : d → Fin (t + 1)}
    (hc1 : ∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1)
    {a b : d} (ha : bl a ≠ 0) (hab : bl a = bl b) : a = b :=
  congrArg Subtype.val ((block_subsingleton hc1 ha).elim ⟨a, rfl⟩ ⟨b, hab.symm⟩)

private theorem tSpan_pullback {O K X X' d G : Type} [CommRing O] [CommRing K] [Algebra O K]
    [Fintype d] [DecidableEq d] [Monoid G]
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (p : X' → X)
    (hTT' : ∀ f ∈ T, (fun y : X' => f (p y)) ∈ T')
    (r₀ : G →* (X → Matrix d d O)) (rK : G →* (X' → Matrix d d K))
    (hrK : ∀ g y, rK g y = (r₀ g (p y)).map (algebraMap O K)) :
    ∀ a ∈ tSpan T r₀, (fun y : X' => (a (p y)).map (algebraMap O K)) ∈ tSpan T' rK := by
  rintro a ⟨S, c, hc, rfl⟩
  refine ⟨S, fun g y => c g (p y), fun g => hTT' _ (hc g), ?_⟩
  funext y; ext i j
  simp [Finset.sum_apply, Matrix.sum_apply, hrK]
  exact Finset.sum_congr rfl fun g _ => (Algebra.smul_def _ _).symm

private theorem tSpan_entries_integral {O K X X' d G : Type} [CommRing O] [CommRing K] [Algebra O K]
    [Fintype d] [DecidableEq d] [Monoid G]
    (T' : Subalgebra O (X' → O)) (p : X' → X)
    (r₀ : G →* (X → Matrix d d O)) (rK : G →* (X' → Matrix d d K))
    (hrK : ∀ g y, rK g y = (r₀ g (p y)).map (algebraMap O K)) :
    ∀ a ∈ tSpan T' rK, ∀ y, ∃ A : Matrix d d O, A.map (algebraMap O K) = a y := by
  rintro a ⟨S, c, hc, rfl⟩ y
  refine ⟨∑ g ∈ S, c g y • r₀ g (p y), ?_⟩
  ext i j
  simp [Finset.sum_apply, Matrix.sum_apply, hrK]
  exact Finset.sum_congr rfl fun g _ => (Algebra.smul_def _ _).symm

private theorem blockPoly_diag_spec {O d : Type} [CommRing O] [Fintype d] [DecidableEq d]
    {t : ℕ} (bl : d → Fin (t + 1)) (γ : ℕ → O)
    (hc1 : ∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1) :
    blockPoly (Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0)
        (Matrix.diagonal fun a => if bl a ≠ 0 then γ ((bl a : ℕ) - 1) else 0) =
      ∏ i : Fin t, (Polynomial.X - Polynomial.C (γ i)) := by
  let F : Fin (t + 1) → Polynomial O :=
    fun c => if c ≠ 0 then Polynomial.X - Polynomial.C (γ ((c : ℕ) - 1)) else 1
  have h1 : blockPoly (Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0)
      (Matrix.diagonal fun a => if bl a ≠ 0 then γ ((bl a : ℕ) - 1) else 0) = ∏ a : d, F (bl a) := by
    unfold blockPoly
    have h2 : ((Polynomial.X : Polynomial O) •
        (Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0).map Polynomial.C -
        (Matrix.diagonal fun a => if bl a ≠ 0 then γ ((bl a : ℕ) - 1) else 0).map Polynomial.C +
        (1 - Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0).map Polynomial.C) =
        Matrix.diagonal fun a => F (bl a) := by
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases hi : bl i = 0 <;> simp [hi, F]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rw [h2, Matrix.det_diagonal]
  have h3 : ∏ a : d, F (bl a) = ∏ c, F c := by
    rw [← Finset.prod_fiberwise univ bl (fun a => F (bl a))]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Finset.prod_congr rfl (fun a ha => by rw [(mem_filter.mp ha).2]), Finset.prod_const]
    by_cases hc : c = 0
    · simp [hc, F]
    · have hcard : #{a ∈ (univ : Finset d) | bl a = c} = 1 := by
        have h := hc1 c hc; rw [Fintype.card_subtype] at h; convert h
      rw [hcard, pow_one]
  rw [h1, h3, Fin.prod_univ_succ]; simp [F, Fin.succ_ne_zero]

private def liftEvalAlgHom {O K X' d : Type} [CommRing O] [CommRing K] [Algebra O K]
    [Fintype d] [DecidableEq d]
    (hι : Function.Injective (algebraMap O K))
    (R' : Subalgebra O (X' → Matrix d d K)) (π' : X')
    (hint : ∀ a : R', ∃ A : Matrix d d O, A.map (algebraMap O K) = a.1 π') :
    R' →ₐ[O] Matrix d d O :=
  let ρf : R' → Matrix d d O := fun a => Classical.choose (hint a)
  have hent : ∀ (a : R') i j, algebraMap O K (ρf a i j) = a.1 π' i j :=
    fun a i j => congrFun (congrFun (Classical.choose_spec (hint a)) i) j
  { toFun := ρf
    map_one' := by
      ext i j; apply hι; rw [hent]
      show (1 : Matrix d d K) i j = algebraMap O K ((1 : Matrix d d O) i j)
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    map_mul' := fun a b => by
      ext i j; apply hι; rw [hent]
      show (a.1 π' * b.1 π') i j = _
      simp only [Matrix.mul_apply, map_sum, map_mul, hent]
    map_zero' := by
      ext i j; apply hι; rw [hent]
      show (0 : Matrix d d K) i j = algebraMap O K ((0 : Matrix d d O) i j); simp
    map_add' := fun a b => by
      ext i j; apply hι; rw [hent]
      show a.1 π' i j + b.1 π' i j = algebraMap O K (ρf a i j + ρf b i j)
      rw [map_add, hent, hent]
    commutes' := fun c => by
      ext i j; apply hι; rw [hent]
      show (algebraMap O (Matrix d d K) c) i j = algebraMap O K ((algebraMap O (Matrix d d O) c) i j)
      by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply] }

private def restrictBlockAlgHom {O R' d : Type} [CommRing O] [Ring R'] [Algebra O R']
    [Fintype d] [DecidableEq d] {t : ℕ} (bl : d → Fin (t + 1))
    (ρπ : R' →ₐ[O] Matrix d d O) (hBD : ∀ (a : R') i j, bl i ≠ bl j → ρπ a i j = 0)
    (k : Fin (t + 1)) : R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O where
  toFun a := (ρπ a).toSquareBlock bl k
  map_one' := by
    rw [map_one]; ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.toSquareBlock_def]
    · simp [Matrix.toSquareBlock_def, Matrix.one_apply, h, show i.1 ≠ j.1 from fun e => h (Subtype.ext e)]
  map_mul' a b := by rw [map_mul]; exact blk_mul bl (hBD a) k
  map_zero' := by rw [map_zero]; ext i j; simp [Matrix.toSquareBlock_def]
  map_add' a b := by rw [map_add]; ext i j; simp [Matrix.toSquareBlock_def]
  commutes' c := by
    rw [AlgHom.commutes]; ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.toSquareBlock_def, Matrix.algebraMap_matrix_apply]
    · simp [Matrix.toSquareBlock_def, Matrix.algebraMap_matrix_apply, h,
        show i.1 ≠ j.1 from fun e => h (Subtype.ext e)]

private theorem finite_splitPts {O X : Type} [CommRing O] [IsDomain O] [Fintype X]
    (t : ℕ) (P : X → Polynomial O) : Finite (SplitPts t P) := by
  let Zs : Finset O := univ.biUnion fun x => (P x).roots.toFinset
  let f : SplitPts t P → X × (Fin t → Zs) := fun y => (y.1.1, fun i => ⟨y.1.2 i, by
    refine mem_biUnion.mpr ⟨y.1.1, mem_univ _, ?_⟩
    have hy : P y.1.1 = ∏ i, (Polynomial.X - Polynomial.C (y.1.2 i)) := y.2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hy ▸ (Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _).ne_zero,
      by rw [Polynomial.IsRoot, hy, Polynomial.eval_prod]; exact Finset.prod_eq_zero (mem_univ i) (by simp)⟩⟩)
  exact Finite.of_injective f fun y y' h =>
    Subtype.ext (Prod.ext (congrArg Prod.fst h) (funext fun i => congrArg (fun z => (z.2 i).1) h))

private theorem blockRep_smul_of_diag {O X' d : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Fintype d] [DecidableEq d] {t : ℕ} {bl : d → Fin (t + 1)}
    {R' : Subalgebra O (X' → Matrix d d (FractionRing O))} {π' : X'}
    {ρπ : R' →ₐ[O] Matrix d d O}
    (hentπ : ∀ (a : R') i j, algebraMap O (FractionRing O) (ρπ a i j) = a.1 π' i j)
    {ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O}
    (hρk : ∀ k (a : R') i j, ρk k a i j = ρπ a i.1 j.1)
    (k : Fin (t + 1)) (a : R') (w : O)
    (h : ∀ i j : {a // bl a = k}, a.1 π' i.1 j.1 = if i = j then algebraMap O (FractionRing O) w else 0)
    (m : blockRestrictedRepresentationType bl ρk k) : a • m = w • m := by
  have hι : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  funext i
  have h1 : ∀ j, ρk k a i j = if i = j then w else 0 := fun j => by
    apply hι; rw [hρk, hentπ, h]; split_ifs <;> simp
  show ∑ j, ρk k a i j • (m j : KO O) = w • (m i : KO O)
  simp only [h1, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem blockAlgHom_surjective {O X' d G : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)}
    {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
    {ρπ : R' →ₐ[O] Matrix d d O}
    {ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O}
    (hρk0 : ∀ a, ρk 0 a = (ρπ a).toSquareBlock bl 0)
    (rR : G →* R') (r₀π : G → Matrix d d O) (hρr : ∀ g, ρπ (rR g) = r₀π g)
    (hA : AbsIrr (fun g => (r₀π g).toSquareBlock bl 0 |>.map (IsLocalRing.residue O)))
    (hc1 : ∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1) :
    ∀ k, Function.Surjective (ρk k) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    let ρ0 : G →* Matrix {a // bl a = 0} {a // bl a = 0} O :=
      ((ρk 0).toRingHom.toMonoidHom).comp rR
    have h0 : (fun g => (ρ0 g).map (IsLocalRing.residue O)) =
        fun g => ((r₀π g).toSquareBlock bl 0).map (IsLocalRing.residue O) := funext fun g => by
      show (ρk 0 (rR g)).map _ = _; rw [hρk0, hρr]
    have hspan := ontoSpan O _ G ρ0 (h0 ▸ hA)
    intro B
    have hle : Submodule.span O (Set.range ρ0) ≤ LinearMap.range (ρk 0).toLinearMap :=
      Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact ⟨rR g, rfl⟩)
    exact hle (hspan ▸ Submodule.mem_top)
  · intro B
    have hs := block_subsingleton hc1 hk
    obtain ⟨i0⟩ := block_nonempty hc1 hk
    refine ⟨algebraMap O R' (B i0 i0), ?_⟩
    rw [AlgHom.commutes]; ext i j
    rw [hs.elim i i0, hs.elim j i0]; simp [Matrix.algebraMap_matrix_apply]

private theorem range_e1_equiv_KO {O X' d : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Fintype d] [DecidableEq d] {t : ℕ} {bl : d → Fin (t + 1)}
    (hKO : StatIdemKO)
    {R' : Subalgebra O (X' → Matrix d d (FractionRing O))} {π' : X'}
    {ρπ : R' →ₐ[O] Matrix d d O}
    (hentπ : ∀ (a : R') i j, algebraMap O (FractionRing O) (ρπ a i j) = a.1 π' i j)
    {ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O}
    (hρk : ∀ k (a : R') i j, ρk k a i j = ρπ a i.1 j.1)
    (e₁' : R') (e₁π : Matrix d d O) (he1e1 : e₁' * e₁' = e₁')
    (he1val : ∀ i j, e₁'.1 π' i j = algebraMap O (FractionRing O) (e₁π i j))
    (he1π : ∀ a b, (bl a ≠ 0 ∨ bl b ≠ 0) → e₁π a b = 0)
    (hrk1 : (e₁π.map (algebraMap O (FractionRing O))).rank = 1) :
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁')) ≃ₗ[O] KO O) := by
  have h1 : DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁' =
      matEnd O (KO O) _ (ρk 0 e₁') := LinearMap.ext fun _ => rfl
  rw [h1]
  refine hKO O _ (ρk 0 e₁') (by rw [← map_mul, he1e1]) ?_
  have h2 : (ρk 0 e₁').map (algebraMap O (FractionRing O)) =
      (e₁π.map (algebraMap O (FractionRing O))).toSquareBlock bl 0 := by
    ext i j; show algebraMap O (FractionRing O) (ρk 0 e₁' i j) = _
    rw [hρk, hentπ, he1val]; rfl
  rw [h2, rank_block bl 0 (e₁π.map (algebraMap O (FractionRing O))) (fun a b hab => by
    show algebraMap O (FractionRing O) (e₁π a b) = 0; rw [he1π a b hab, map_zero])]
  exact hrk1

private theorem splitPts_fiber_unique {O X d : Type} [CommRing O] [IsDomain O]
    [Fintype d] [DecidableEq d] (t : ℕ) (P : X → Polynomial O)
    (eB X0 : X → Matrix d d O)
    (hPK : ∀ x, (P x).map (algebraMap O (FractionRing O)) =
      blockPoly ((eB x).map (algebraMap O (FractionRing O))) ((X0 x).map (algebraMap O (FractionRing O))))
    (x : X) (α : ℕ → O)
    (h : blockPoly ((eB x).map (algebraMap O (FractionRing O))) ((X0 x).map (algebraMap O (FractionRing O))) =
      ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (algebraMap O (FractionRing O) (α i)))) :
    ∃! y : SplitPts t P, y.1.1 = x ∧ ∀ i (hi : i < t), y.1.2 ⟨i, hi⟩ = α i := by
  have hι : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  have hPx : P x = ∏ i : Fin t, (Polynomial.X - Polynomial.C (α i)) := by
    apply Polynomial.map_injective (algebraMap O (FractionRing O)) hι
    rw [hPK, Polynomial.map_prod]
    refine h.trans ?_
    rw [Finset.prod_range]
    exact Finset.prod_congr rfl fun i _ => by simp
  refine ⟨⟨(x, fun i => α i), hPx⟩, ⟨rfl, fun _ _ => rfl⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  exact Subtype.ext (Prod.ext hy1 (funext fun i => hy2 i.1 i.2))

private theorem mkRingInst {O X' d G : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite X'] [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)}
    (T' : Subalgebra O (X' → O)) (rK : G →* (X' → Matrix d d (FractionRing O))) (π' : X')
    (ρπ : spanSub T' rK →ₐ[O] Matrix d d O)
    (hentπ : ∀ (a : spanSub T' rK) i j, algebraMap O (FractionRing O) (ρπ a i j) = a.1 π' i j)
    (ρk : ∀ k : Fin (t + 1), spanSub T' rK →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    (hρk : ∀ k (a : spanSub T' rK) i j, ρk k a i j = ρπ a i.1 j.1)
    (hint : ∀ a ∈ tSpan T' rK, ∀ y, ∃ A : Matrix d d O, A.map (algebraMap O (FractionRing O)) = a y) :
    letI : Algebra T' (spanSub T' rK) := algRp T' rK
    letI : ∀ x', Module T' (EvalSp O d (spanSub T' rK) x') := modEvRp T' rK
    letI : ∀ k, Module T' (blockRestrictedRepresentationType bl ρk k) := fun _ =>
      Module.compHom _ ((Pi.evalRingHom (fun _ : X' => O) π').comp T'.val.toRingHom)
    IsNoetherian (spanSub T' rK) (spanSub T' rK) ∧
      (∀ x', IsScalarTower T' (spanSub T' rK) (EvalSp O d (spanSub T' rK) x')) ∧
      (∀ k, SMulCommClass (spanSub T' rK) O (blockRestrictedRepresentationType bl ρk k)) ∧
      (∀ k, IsScalarTower T' (spanSub T' rK) (blockRestrictedRepresentationType bl ρk k)) ∧
      (∀ k, IsScalarTower O (spanSub T' rK) (blockRestrictedRepresentationType bl ρk k)) := by
  let R' := spanSub T' rK
  let ι := algebraMap O (FractionRing O)
  have hι : Function.Injective ι := IsFractionRing.injective O (FractionRing O)
  letI : Algebra T' R' := algRp T' rK
  letI : ∀ x', Module T' (EvalSp O d R' x') := modEvRp T' rK
  letI : ∀ k, Module T' (blockRestrictedRepresentationType bl ρk k) := fun _ =>
    Module.compHom _ ((Pi.evalRingHom (fun _ : X' => O) π').comp T'.val.toRingHom)
  have hsv : ∀ (f : T') (a : R') y, (f • a : R').1 y = ι (f.1 y) • a.1 y := smul_val T' rK
  refine ⟨noeth O X' d R' (fun a ha x' i j => by
      obtain ⟨A, hA'⟩ := hint a ha x'; exact ⟨A i j, congrFun (congrFun hA' i) j⟩),
    fun x' => ⟨fun f a v => by
      funext i; show ∑ j, (f • a : R').1 x' i j • (v j : FractionRing O) = ι (f.1 x') • ∑ j, a.1 x' i j • (v j : FractionRing O)
      rw [hsv, Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => by simp [mul_assoc]⟩,
    fun k => ⟨fun a c m => LinearMap.map_smul (matEnd O (KO O) _ ((ρk k).toRingHom a)) c m⟩,
    fun k => ⟨fun f a m => by
      funext i; show ∑ j, ρk k (f • a) i j • (m j : KO O) = f.1 π' • ∑ j, ρk k a i j • (m j : KO O)
      rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      have hsm : ρπ (f • a) i.1 j.1 = f.1 π' * ρπ a i.1 j.1 := by
        apply hι; rw [hentπ, hsv, map_mul, hentπ]; rfl
      rw [hρk, hρk, hsm, mul_smul]⟩,
    fun k => ⟨fun c a m => by
      funext i; show ∑ j, ρk k (c • a) i j • (m j : KO O) = c • ∑ j, ρk k a i j • (m j : KO O)
      rw [Finset.smul_sum, map_smul]
      exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul, mul_smul]⟩⟩

private theorem basis_lin_indep_pullback {O X X' : Type} [CommRing O]
    (p : X' → X) {q : ℕ} (b : Fin q → X' → O)
    (hb2 : ∀ x, ∀ a : Fin q → O, (∀ y : X', p y = x → ∑ k, a k * b k y = 0) → a = 0)
    (a : Fin q → X → O) (h0 : ∑ k, (a k ∘ p) * b k = 0) : a = 0 := by
  funext k x
  refine congrFun (hb2 x (fun k => a k x) fun x' hx' => ?_) k
  have h1 := congrFun h0 x'
  rw [Finset.sum_apply] at h1
  rwa [← hx']

/-! ### 3. Refactored Main Theorem `ring_objects_of_matrix_data` (EXACT Original Statement, Zero `sorry`) -/

set_option maxHeartbeats 2000000 in
theorem ring_objects_of_matrix_data (hEM : StatEMat) (hSP : StatSplitPts) (hKO : StatIdemKO) : RingObjectsExist := by
  intro O _ _ _ X _ T d _ _ G _ r₀ π t ht bl χ₁ ε hP hA eB e₁ hI g₀ s hX
  obtain ⟨hloc, hpts, hG1, hbd, hc1, hχ⟩ := hP
  obtain ⟨heBm, he1m, heBB, he11, heB1, he1B, hrkB, hrk1, heBπ, he1π⟩ := hI
  obtain ⟨hsm, hes, hse, hsπ, hroots⟩ := hX
  let K := FractionRing O
  let ι : O →+* K := algebraMap O K
  have hι : Function.Injective ι := IsFractionRing.injective O K

  -- Stage 1: Characteristic block polynomial `P`, splitting cover `X'`, and extended base `T'`
  let X0 : X → Matrix d d O := eB * r₀ g₀ * eB + s
  have hX0m : X0 ∈ tSpan T r₀ := add_mem_tSpan T r₀
    (mul_mem_tSpan T r₀ (mul_mem_tSpan T r₀ heBm (r_mem T r₀ g₀)) heBm) hsm
  let P : X → Polynomial O := fun x => blockPoly (eB x) (X0 x)
  have hPc : ∀ k, (fun x => (P x).coeff k) ∈ T := blockPolyT O X T d G r₀ hG1 eB heBm X0 hX0m
  have hPK : ∀ x, (P x).map ι = blockPoly ((eB x).map ι) ((X0 x).map ι) := fun x => blockPoly_map ι _ _
  have hPr : ∀ x, ∃ α : Fin t → O, Function.Injective α ∧ P x = ∏ i, (Polynomial.X - Polynomial.C (α i)) := fun x => by
    obtain ⟨α, hα, h⟩ := hroots x
    obtain ⟨β, hβ, hPβ⟩ := rootsInt O (P x) t α (hPK x ▸ h)
    exact ⟨β, fun i j hij => hα (by rw [← hβ, ← hβ, hij]), hPβ⟩
  obtain ⟨b, hb0, hb1, hb2⟩ := hSP O X T t P hPc hPr
  let X' := SplitPts t P
  let p : X' → X := fun y => y.1.1
  let T' : Subalgebra O (X' → O) := splitT T t P
  have hTT' : ∀ f ∈ T, (fun y : X' => f (p y)) ∈ T' := fun f hf => Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)
  let rr : ℕ → T' := fun i =>
    if h : i < t then ⟨splitRoot t P ⟨i, h⟩, Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)⟩ else 0
  have hrr : ∀ i (h : i < t) (y : X'), (rr i).1 y = y.1.2 ⟨i, h⟩ := fun i h y => by simp only [rr, dif_pos h]; rfl

  -- Stage 2: Pulled-back matrix algebra `R'`, special fiber point `π'`, and lifted block homs `ρπ`, `ρk`
  let rK : G →* (X' → Matrix d d K) :=
    { toFun := fun g y => (r₀ g (p y)).map ι
      map_one' := by funext y; simp
      map_mul' := fun g h => by funext y; simp [Matrix.map_mul] }
  let R' : Subalgebra O (X' → Matrix d d K) := spanSub T' rK
  letI iA : Algebra T' R' := algRp T' rK
  letI iE : ∀ x', Module T' (EvalSp O d R' x') := modEvRp T' rK
  have hpull : ∀ a ∈ tSpan T r₀, (fun y : X' => (a (p y)).map ι) ∈ tSpan T' rK :=
    tSpan_pullback T T' p hTT' r₀ rK (fun _ _ => rfl)
  have hint : ∀ a ∈ tSpan T' rK, ∀ y, ∃ A : Matrix d d O, A.map ι = a y :=
    tSpan_entries_integral T' p r₀ rK (fun _ _ => rfl)
  let γ : ℕ → O := fun i => (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)
  have heBπ' : eB π = Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0 := by
    rw [heBπ]; congr 1; funext a; by_cases h : bl a = 0 <;> simp [h]
  have hX0π : X0 π = Matrix.diagonal fun a => if bl a ≠ 0 then γ ((bl a : ℕ) - 1) else 0 := by
    show eB π * r₀ g₀ π * eB π + s π = _; rw [hsπ, add_zero, heBπ']; ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : i = j
    · subst hij; by_cases hi : bl i = 0 <;> simp [hi, hχ g₀ i, γ]
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hb : bl i = bl j
      · have hi : bl i = 0 := by by_contra hi; exact hij (block_inj_of_ne_zero hc1 hi hb)
        simp [hi]
      · rw [hbd g₀ i j hb]; simp
  have hPπ : P π = ∏ i : Fin t, (Polynomial.X - Polynomial.C (γ i)) := by
    show blockPoly (eB π) (X0 π) = _; rw [heBπ', hX0π]; exact blockPoly_diag_spec bl γ hc1
  let π' : X' := ⟨(π, fun i => γ i), hPπ⟩
  have hrrπ : ∀ i, i < t → (rr i).1 π' = γ i := fun i h => hrr i h π'
  let ρπ : R' →ₐ[O] Matrix d d O := liftEvalAlgHom hι R' π' (fun a => hint a.1 a.2 π')
  have hρf : ∀ a : R', (ρπ a).map ι = a.1 π' := fun a => Classical.choose_spec (hint a.1 a.2 π')
  have hentπ : ∀ (a : R') i j, ι (ρπ a i j) = a.1 π' i j := fun a i j => congrFun (congrFun (hρf a) i) j
  have hBD : ∀ (a : R') i j, bl i ≠ bl j → ρπ a i j = 0 := fun a i j hij => by
    apply hι; rw [hentπ, map_zero]
    rcases a.2 with ⟨S, c, _, hS⟩
    rw [← hS]; simp [Finset.sum_apply, Matrix.sum_apply, rK, ι, hbd _ i j hij]
  let ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O :=
    restrictBlockAlgHom bl ρπ hBD
  letI iB : ∀ k, Module T' (blockRestrictedRepresentationType bl ρk k) := fun k =>
    Module.compHom _ ((Pi.evalRingHom (fun _ : X' => O) π').comp T'.val.toRingHom)
  have hTB : ∀ (f : T') k (m : blockRestrictedRepresentationType bl ρk k), f • m = (f.1 π') • m := fun _ _ _ => rfl
  have hTE : ∀ (f : T') x' (v : EvalSp O d R' x'), f • v = ι (f.1 x') • v := fun _ _ _ => rfl

  -- Stage 3: Lagrange projector `E`, discriminant `δ`, pointwise rank-1 properties, and special-fiber eigenvalues
  let rR : G →* R' :=
    { toFun := fun g => ⟨rK g, r_mem' T' rK g⟩
      map_one' := Subtype.ext (map_one rK)
      map_mul' := fun g h => Subtype.ext (map_mul rK g h) }
  let χ : G →* (T')ˣ := (Units.map (algebraMap O T').toMonoidHom).comp χ₁
  let eB' : R' := ⟨fun y => (eB (p y)).map ι, hpull eB heBm⟩
  let e₁' : R' := ⟨fun y => (e₁ (p y)).map ι, hpull e₁ he1m⟩
  let X₀' : R' := ⟨fun y => (X0 (p y)).map ι, hpull X0 hX0m⟩
  let E : R' := eB' * ((List.range t).tail.map fun i => X₀' - rr i • eB').prod
  let δ : T' := ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i)
  have hsv : ∀ (f : T') (a : R') y, (f • a : R').1 y = ι (f.1 y) • a.1 y := smul_val T' rK
  have hEy : ∀ y, E.1 y = eB'.1 y *
      ((List.range t).tail.map fun i => X₀'.1 y - ι ((rr i).1 y) • eB'.1 y).prod := fun y => by
    show evalAt O d R' y E = _; rw [map_mul, map_list_prod, List.map_map]
    exact congrArg₂ _ rfl (congrArg List.prod (List.map_congr_left fun i _ => by
      show X₀'.1 y - (rr i • eB' : R').1 y = _; rw [hsv]))
  have hδy : ∀ y, ι (δ.1 y) = ∏ i ∈ Finset.Ioo 0 t, (ι ((rr 0).1 y) - ι ((rr i).1 y)) := fun y => by
    have h1 : δ.1 y = ∏ i ∈ Finset.Ioo 0 t, ((rr 0).1 y - (rr i).1 y) := by
      show ((Pi.evalRingHom (fun _ : X' => O) y).comp T'.val.toRingHom) δ = _; rw [map_prod]; rfl
    rw [h1, map_prod]; simp only [map_sub]
  have hmapmul : ∀ (u v w : X → Matrix d d O), u * v = w → ∀ x, (u x).map ι * (v x).map ι = (w x).map ι :=
    fun _ _ _ h x => by rw [← Matrix.map_mul, ← h]; rfl
  have hpoly : ∀ y : X', blockPoly (eB'.1 y) (X₀'.1 y) =
      ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (ι ((rr i).1 y))) := fun y => by
    show blockPoly ((eB (p y)).map ι) ((X0 (p y)).map ι) = _
    rw [← hPK, show P (p y) = _ from y.2, Polynomial.map_prod, Finset.prod_range]
    exact Finset.prod_congr rfl fun i _ => by rw [hrr i.1 i.2 y]; simp
  have hpt : ∀ y : X', E.1 y * E.1 y = ι (δ.1 y) • E.1 y ∧ (E.1 y).rank = 1 ∧ ι (δ.1 y) ≠ 0 := fun y => by
    have hyinj : Function.Injective y.1.2 := by
      obtain ⟨α, hα, hPα⟩ := hPr (p y)
      have h2 : (P (p y)).map ι = ∏ i, (Polynomial.X - Polynomial.C (ι (y.1.2 i))) := by
        rw [show P (p y) = _ from y.2, Polynomial.map_prod]; simp
      have h3 : (P (p y)).map ι = ∏ i, (Polynomial.X - Polynomial.C (ι (α i))) := by
        rw [hPα, Polynomial.map_prod]; simp
      exact fun i j hij => inj_of_prod_eq _ _ (hι.comp hα) (h2.symm.trans h3) (congrArg ι hij)
    have heX0 : eB * X0 = X0 := by show eB * (eB * r₀ g₀ * eB + s) = _; rw [mul_add, hes, ← mul_assoc, ← mul_assoc, heBB]
    have hX0e : X0 * eB = X0 := by show (eB * r₀ g₀ * eB + s) * eB = _; rw [add_mul, hse, mul_assoc, heBB]
    obtain ⟨h1, h2, -, -, -, h6⟩ := hEM K d (eB'.1 y) (X₀'.1 y) t (fun i => ι ((rr i).1 y)) ht
      (hmapmul eB eB eB heBB (p y)) (hmapmul eB X0 X0 heX0 (p y)) (hmapmul X0 eB X0 hX0e (p y))
      (hpoly y) (fun i j hi hj hij => by
        rw [hrr i hi, hrr j hj] at hij; exact congrArg Fin.val (hyinj (hι hij)))
    rw [hEy, hδy]; exact ⟨h1, h2, h6⟩

  -- Stage 4: Special fiber diagonal values of `E`, block scalar actions, and `τ`
  let δO : O := δ.1 π'
  let val : d → K := fun a => if bl a ≠ 0 then
    ∏ i ∈ Finset.Ioo 0 t, (ι (γ ((bl a : ℕ) - 1)) - ι ((rr i).1 π')) else 0
  have hEπ : E.1 π' = Matrix.diagonal val := by
    rw [hEy, show eB'.1 π' = (eB π).map ι from rfl, heBπ', map_diagonal_ite ι (fun a => bl a ≠ 0) (fun _ => (1 : O)),
      show X₀'.1 π' = (X0 π).map ι from rfl, hX0π, map_diagonal_ite ι (fun a => bl a ≠ 0) (fun a => γ ((bl a : ℕ) - 1))]
    simpa only [map_one] using eDiag' K d (fun a => bl a ≠ 0) (fun a => ι (γ ((bl a : ℕ) - 1))) t (fun i => ι ((rr i).1 π'))
  have hval1 : ∀ a, (bl a : ℕ) = 1 → val a = ι δO := fun a h => by
    have h0 : bl a ≠ 0 := fun e => by rw [e] at h; simp at h
    simp only [val, if_pos h0, h, Nat.sub_self]; rw [hδy, hrrπ 0 (by omega)]
  have hEblk : ∀ k (w : O), (∀ a, bl a = k → val a = ι w) →
      ∀ m : blockRestrictedRepresentationType bl ρk k, E • m = w • m := fun k w h =>
    blockRep_smul_of_diag hentπ (fun _ _ _ _ => rfl) k E w fun i j => by
      rw [hEπ, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp [h i.1 i.2]
      · simp [hij, show i.1 ≠ j.1 from fun e => hij (Subtype.ext e)]
  have he1blk : ∀ k, k ≠ 0 → ∀ m : blockRestrictedRepresentationType bl ρk k, e₁' • m = 0 := fun k hk m => by
    rw [blockRep_smul_of_diag hentπ (fun _ _ _ _ => rfl) k e₁' 0 (fun i j => by
      show ι (e₁ π i.1 j.1) = _; rw [he1π i.1 j.1 (Or.inl (i.2.symm ▸ hk))]; simp) m, zero_smul]
  obtain ⟨sE, cE, hcE, hEsum⟩ := (E.2 : E.1 ∈ tSpan T' rK)
  let tE : G → T' := fun g => ⟨cE g, hcE g⟩
  have hEs : E = ∑ g ∈ sE, tE g • rR g := Subtype.ext (by
    show E.1 = R'.val (∑ g ∈ sE, tE g • rR g); rw [hEsum, map_sum]
    exact Finset.sum_congr rfl fun g _ => funext fun y => (hsv (tE g) (rR g) y).symm)
  let τ : T' := ∑ g ∈ sE, tE g * ((χ g : (T')ˣ) : T')
  let c1 : Fin (t + 1) := ⟨1, by omega⟩
  have hc10 : c1 ≠ 0 := fun e => by simpa [c1] using congrArg Fin.val e
  have hτ : τ.1 π' = δO := by
    obtain ⟨a1⟩ := block_nonempty hc1 hc10
    apply hι
    have h1 : τ.1 π' = ∑ g ∈ sE, cE g π' * (χ₁ g : O) := by
      show ((Pi.evalRingHom (fun _ : X' => O) π').comp T'.val.toRingHom) τ = _; rw [map_sum]; rfl
    have h2 : E.1 π' a1.1 a1.1 = ι δO := by rw [hEπ, Matrix.diagonal_apply_eq]; exact hval1 a1.1 (by rw [a1.2])
    rw [← h2, hEsum, h1, map_sum]; simp only [Finset.sum_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    show _ = ι (cE g π') • ι (r₀ g π a1.1 a1.1)
    rw [hχ g a1.1 (by rw [a1.2]; exact hc10), a1.2]; simp [c1]

  -- Stage 5: Noetherianity, scalar-tower instances, surjectivity, `KO` range, and `uElt` action
  haveI : Finite X' := finite_splitPts t P
  obtain ⟨i1, i2, i3, i4, i5⟩ := mkRingInst T' rK π' ρπ hentπ ρk (fun _ _ _ _ => rfl) hint
  have hsurj : ∀ k, Function.Surjective (ρk k) :=
    blockAlgHom_surjective (fun _ => rfl) rR (fun g => r₀ g π)
      (fun g => by ext i j; apply hι; rw [hentπ]; rfl) hA hc1
  have he1e1 : e₁' * e₁' = e₁' := Subtype.ext (funext fun y => hmapmul e₁ e₁ e₁ he11 (p y))
  have hKO1 := range_e1_equiv_KO hKO hentπ (fun _ _ _ _ => rfl) e₁' (e₁ π) he1e1
    (fun _ _ => rfl) he1π (hrk1 π)
  have hu1 : ∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt rR χ g • m = m := fun g m => by
    have hs := block_subsingleton hc1 hc10
    rw [blockRep_smul_of_diag hentπ (fun _ _ _ _ => rfl) c1 (uElt rR χ g) 1 (fun i j => by
      rw [if_pos (hs.elim i j), hs.elim j i]
      show ((((χ g)⁻¹ : (T')ˣ) : T') • rR g : R').1 π' i.1 i.1 = ι 1
      rw [hsv, show (((χ g)⁻¹ : (T')ˣ) : T').1 π' = (((χ₁ g)⁻¹ : Oˣ) : O) from by rw [← map_inv, ← map_inv]; rfl]
      show ι _ • ι (r₀ g π i.1 i.1) = ι 1
      rw [hχ g i.1 (by rw [i.2]; exact hc10), i.2]
      have h0 : ((c1 : Fin (t + 1)) : ℕ) - 1 = 0 := rfl
      rw [h0, pow_zero, Units.val_one, mul_one, smul_eq_mul, ← map_mul, Units.inv_mul]) m, one_smul]
  have hG1' : ∀ (g : G) (k : ℕ), FromT T' (fun x => (Matrix.charpolyRev (rK g x)).coeff k) :=
    fun g k => ⟨fun y => (Matrix.charpolyRev (r₀ g (p y))).coeff k, hTT' _ (hG1 g k), fun y => by
      show ι _ = (Matrix.charpolyRev ((r₀ g (p y)).map ι)).coeff k
      rw [← charpolyRev_map, Polynomial.coeff_map]⟩

  -- Stage 6: Final assembly of `RingData`, `RingDef`, `RingInst`, and `RingTop`
  let D : RingData O X d G t bl :=
    { X' := X', T' := T', p := p, q := t.factorial, b := b, R' := R', algT := iA, modEv := iE,
      r := rR, χ := χ, eB := eB', e₁ := e₁', X₀ := X₀', E := E, rr := rr, π' := π', ρπ := ρπ,
      ρk := ρk, blockModuleStructure := iB, sE := sE, tE := tE }
  refine ⟨D, ⟨hpoly, ?_, ?_, rfl, rfl, hrrπ, fun _ _ => rfl, ?_, hsv, hTE, hTB, fun _ _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, hρf, fun _ _ => rfl, hb0, hb1,
    fun a _ h0 => basis_lin_indep_pullback p b hb2 a h0, hEs⟩,
    ⟨i1, i2, i3, i4, i5⟩, i3, ?_⟩
  · intro x α h
    obtain ⟨y, ⟨hy1, hy2⟩, huniq⟩ := splitPts_fiber_unique t P eB X0 hPK x α h
    exact ⟨y, ⟨hy1, fun i hi => by rw [hrr i hi]; exact hy2 i hi⟩,
      fun y' ⟨hy1', hy2'⟩ => huniq y' ⟨hy1', fun i hi => by rw [← hrr i hi]; exact hy2' i hi⟩⟩
  · show Algebra.adjoin O _ = Algebra.adjoin O _
    congr 2; ext f'
    exact ⟨fun ⟨i, hi⟩ => ⟨i.1, i.2, hi ▸ funext fun y => (hrr i.1 i.2 y).symm⟩,
      fun ⟨i, hi, hf⟩ => ⟨⟨i, hi⟩, hf ▸ funext fun y => (hrr i hi y).symm⟩⟩
  · intro a
    show a ∈ R' ↔ a ∈ tSpan T' (R'.val.toRingHom.toMonoidHom.comp rR)
    rw [show (R'.val.toRingHom.toMonoidHom.comp rR) = rK from MonoidHom.ext fun _ => rfl]; exact Iff.rfl
  · show RingTop O X X' T T' p t.factorial b d R' T' G rR χ E e₁' δ π' ρπ t ht bl ρk sE tE δO
    refine ⟨hb1, hb2, fun g _ _ Θ => eta_determinant_comparison det_poly_statement blockDet O X' G T' d R' rK hG1'
      (fun _ ha => ha) g Θ, ?_, he1e1, ?_, hρf, fun a i j hij => hBD a i j (ne_of_gt hij), hsurj,
      fun _ _ => rfl, hc1, hEs,
      fun m => by rw [hEblk 0 0 (fun a ha => by simp [val, ha]) m, zero_smul],
      fun m => hTB δ 0 m, fun m => by rw [hTB τ 0 m, hτ], hKO1, ?_, hu1, he1blk c1 hc10,
      hEblk c1 δO (fun a ha => hval1 a (by rw [ha])), fun m => hTB δ c1 m⟩
    · exact Subtype.ext (funext fun y => by
        show E.1 y * E.1 y = (scal T' rK δ).1 y * E.1 y
        rw [(hpt y).1, scal_apply, Matrix.smul_mul, Matrix.one_mul])
    · exact fun x' => ⟨ι (δ.1 x'), (hpt x').2.2, fun v => hTE δ x' v,
        by rw [finrank_range_eq]; exact (hpt x').2.1, by rw [finrank_range_eq]; exact hrk1 (p x')⟩
    · intro c hc
      have hc0 : c ≠ 0 := fun e => by rw [e] at hc; simp at hc
      refine ⟨he1blk c hc0, fun m => ?_, fun m => hTB δ c m, fun m => by rw [hTB τ c m, hτ]⟩
      rw [hEblk c 0 (fun a ha => by
        have h0 : bl a ≠ 0 := ha.symm ▸ hc0
        have hlt : (bl a : ℕ) - 1 < t := by have := (bl a).2; omega
        simp only [val, if_pos h0, map_zero]
        refine Finset.prod_eq_zero (i := (bl a : ℕ) - 1) (Finset.mem_Ioo.mpr ⟨by omega, hlt⟩) ?_
        rw [hrrπ _ hlt, sub_self]) m, zero_smul]

end Formalism.RepresentationBoundsCohomology.ringDataObjects
