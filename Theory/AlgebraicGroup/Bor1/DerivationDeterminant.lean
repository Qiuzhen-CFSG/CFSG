module

public import Mathlib.GroupTheory.Perm.Support
public import Theory.AlgebraicGroup.Bor1.DerivationFinsetProduct

universe u w

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- At a matrix whose value at the identity is the identity matrix, the
derivative of its determinant is the sum of the diagonal derivatives. -/
public theorem identityPointDerivation_det_at_identity
    {G : Variety k} [AlgebraicGroup G] (D : IdentityPointDerivation G)
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι G.PolynomialFunction)
    (hM : ∀ i j, M i j 1 = if i = j then 1 else 0) :
    D M.det = ∑ i, D (M i i) := by
  classical
  rw [Matrix.det_apply', map_sum]
  simp_rw [D.leibniz]
  simp only [Derivation.map_intCast]
  have hsmul (f : G.PolynomialFunction) (c : k) :
      f • c = f 1 * c := rfl
  simp_rw [hsmul]
  simp only [mul_zero, add_zero]
  simp_rw [identityPointDerivation_prod D Finset.univ]
  have hcast (z : ℤ) : ((z : G.PolynomialFunction) 1) = (z : k) := by
    exact map_intCast (polynomialFunctionPointAlgHom G 1) z
  simp_rw [hcast, hM]
  rw [Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp
  · intro σ hσ hne
    suffices (∑ i, (∏ j ∈ Finset.univ.erase i,
        if σ j = j then (1 : k) else 0) * D (M (σ i) i)) = 0 by
      rw [this, mul_zero]
    apply Finset.sum_eq_zero
    intro i hi
    suffices (∏ j ∈ Finset.univ.erase i,
        if σ j = j then (1 : k) else 0) = 0 by
      rw [this, zero_mul]
    have hmoved : ∃ j, j ≠ i ∧ σ j ≠ j := by
      by_contra h
      push Not at h
      have hsupport : σ.support ⊆ {i} := by
        intro j hj
        by_contra hji
        exact (Equiv.Perm.mem_support.mp hj)
          (h j (Finset.notMem_singleton.mp hji))
      have hcard : σ.support.card ≤ 1 := by
        calc
          σ.support.card ≤ ({i} : Finset ι).card :=
            Finset.card_le_card hsupport
          _ = 1 := Finset.card_singleton i
      exact hne (Equiv.Perm.card_support_le_one.mp hcard)
    obtain ⟨j, hji, hj⟩ := hmoved
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    simp [hj]
  · simp

end Theory.AlgebraicGroup.Bor1
