module
public import Theory.AlgebraicGroup.RootSystems.IntegralGeckConstruction

/-!
# Row formulas for the integral Geck comparison

The root-to-root entry of a positive Geck operator is the bottom string
length at its output root. A linear projection therefore collapses a row of
its product with a root-incidence matrix to one scalar coefficient, even
when the projection is not injective. The proof uses uniqueness of the
predecessor root and the actual root-string recurrence.

The remaining lemmas evaluate the Cartan rows and the sign involution on
rectangular matrices without unfolding the concrete finite root sets.
Their consumer is the E6--F4 comparison in `FirstOrder`.

Sources: integral Geck construction; GLS3 §§2.2--2.6.
-/

noncomputable section
attribute [local instance] Classical.decEq
namespace RootPairing.IntegralGeckConstruction
variable {ι M N V κ : Type*} [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N] [AddCommGroup V] [Module ℝ V]
  {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

public theorem eMatrix_root_row (i : b.support) (r t : ι) :
    eMatrix i (.inr r) (.inr t) =
      if P.root r = P.root i + P.root t then (P.chainBotCoeff i r : ℤ) else 0 := by
  classical
  change (if P.root r = P.root i + P.root t then (P.chainBotCoeff i t : ℤ) + 1 else 0) = _
  split_ifs with h
  · have hlin := P.linearIndependent_of_add_mem_range_root' ⟨r, h⟩
    rw [P.chainBotCoeff_of_add hlin (h.trans (add_comm _ _)), Nat.cast_add, Nat.cast_one]
  · rfl

public theorem eMatrix_root_row_project (i : b.support) (r : ι)
    (f : M →ₗ[ℝ] V) (y : V) :
    (∑ t : ι, eMatrix i (.inr r) (.inr t) * (if f (P.root t) = y then 1 else 0)) =
      if f (P.root r) = f (P.root i) + y then (P.chainBotCoeff i r : ℤ) else 0 := by
  classical
  simp_rw [eMatrix_root_row]
  by_cases h : ∃ t, P.root r = P.root i + P.root t
  · obtain ⟨t, ht⟩ := h
    have he (u : ι) : P.root r = P.root i + P.root u ↔ u = t := by
      rw [ht, add_left_cancel_iff]
      exact ⟨fun h => P.root.injective h.symm, fun h => h ▸ rfl⟩
    simp only [he, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [ht, map_add, add_left_cancel_iff]
    split_ifs <;> simp
  · have hz : P.chainBotCoeff i r = 0 := by
      apply P.chainBotCoeff_eq_zero_iff.mpr
      right
      rintro ⟨t, ht⟩
      exact h ⟨t, by rw [ht]; abel⟩
    have hn (t : ι) : P.root r ≠ P.root i + P.root t := fun ht => h ⟨t, ht⟩
    simp [hn, hz]

omit [P.IsCrystallographic] [P.IsReduced] in
public theorem omega_mul_inl (A : Matrix (b.support ⊕ ι) κ ℤ) (i : b.support) (k : κ) :
    (omegaMatrix (b := b) * A) (.inl i) k = A (.inl i) k := by
  classical
  simp [Matrix.mul_apply, Fintype.sum_sum_type, omegaMatrix, Matrix.one_apply]

omit [P.IsCrystallographic] [P.IsReduced] in
public theorem omega_mul_inr (A : Matrix (b.support ⊕ ι) κ ℤ) (i : ι) (k : κ) :
    (omegaMatrix (b := b) * A) (.inr i) k = A (.inr (P.reflectionPerm i i)) k := by
  classical
  let := P.indexNeg
  have he (j : ι) : i = P.reflectionPerm j j ↔ j = P.reflectionPerm i i := by
    change i = -j ↔ j = -i
    constructor <;> intro h <;> simpa only [neg_neg] using (congrArg Neg.neg h).symm
  simp [Matrix.mul_apply, Fintype.sum_sum_type, omegaMatrix, he]

omit [P.IsCrystallographic] [P.IsReduced] in
public theorem mul_omega_inl (A : Matrix κ (b.support ⊕ ι) ℤ) (k : κ) (i : b.support) :
    (A * omegaMatrix (b := b)) k (.inl i) = A k (.inl i) := by
  classical
  simp [Matrix.mul_apply, Fintype.sum_sum_type, omegaMatrix, Matrix.one_apply]

omit [P.IsCrystallographic] [P.IsReduced] in
public theorem mul_omega_inr (A : Matrix κ (b.support ⊕ ι) ℤ) (k : κ) (i : ι) :
    (A * omegaMatrix (b := b)) k (.inr i) = A k (.inr (P.reflectionPerm i i)) := by
  classical
  let := P.indexNeg
  simp [Matrix.mul_apply, Fintype.sum_sum_type, omegaMatrix]

omit [P.IsReduced] in
public theorem eMatrix_mul_cartan_row (A : Matrix (b.support ⊕ ι) κ ℤ)
    (i j : b.support) (k : κ) :
    (eMatrix i * A) (.inl j) k =
      if j = i then A (.inr (P.reflectionPerm i i)) k else 0 := by
  classical
  by_cases h : j = i
  · subst j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, eMatrix]
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, eMatrix, h]

omit [P.IsReduced] in
public theorem eMatrix_mul_root_row (A : Matrix (b.support ⊕ ι) κ ℤ)
    (i : b.support) (r : ι) (k : κ) :
    (eMatrix i * A) (.inr r) k =
      (if r = i then ∑ j : b.support, |b.cartanMatrix i j| * A (.inl j) k else 0) +
      ∑ t : ι, eMatrix i (.inr r) (.inr t) * A (.inr t) k := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  congr 1
  by_cases h : r = i <;> simp [eMatrix, h]

end RootPairing.IntegralGeckConstruction
