module

public import Theory.AlgebraicGroup.Bor1.DerivationDeterminant

universe u w

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Replace one row of an identity-valued square minor by a row outside its
column set.  The derivative of the resulting determinant is exactly the
derivative of the replacement entry in the matching column. -/
public theorem identityPointDerivation_det_singleRowReplacement
    {G : Variety k} [AlgebraicGroup G] (D : IdentityPointDerivation G)
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (c : Fin n ↪ ι) (i₀ : Fin n) (a : ι)
    (ha : a ∉ Set.range c)
    (M : Matrix ι ι G.PolynomialFunction)
    (hM : ∀ i j, M i j 1 = if i = j then 1 else 0) :
    D (Matrix.det fun i j : Fin n =>
      M (Function.update (fun x => c x) i₀ a i) (c j)) =
      D (M a (c i₀)) := by
  classical
  let r : Fin n → ι := Function.update (fun x => c x) i₀ a
  let N : Matrix (Fin n) (Fin n) G.PolynomialFunction :=
    fun i j => M (r i) (c j)
  have hN (i j : Fin n) :
      N i j 1 = if i = i₀ then 0 else if i = j then 1 else 0 := by
    dsimp [N]
    rw [hM]
    by_cases hi : i = i₀
    · subst i
      rw [show r i₀ = a by simp [r]]
      have haj : a ≠ c j := by
        intro h
        exact ha ⟨j, h.symm⟩
      simp [haj]
    · rw [show r i = c i by simp [r, hi]]
      simp [hi, c.injective.eq_iff]
  change D N.det = D (M a (c i₀))
  rw [Matrix.det_apply', map_sum]
  simp_rw [D.leibniz]
  simp only [Derivation.map_intCast]
  have hsmul (f : G.PolynomialFunction) (z : k) :
      f • z = f 1 * z := rfl
  simp_rw [hsmul]
  simp only [mul_zero, add_zero]
  simp_rw [identityPointDerivation_prod D Finset.univ]
  have hcast (z : ℤ) : ((z : G.PolynomialFunction) 1) = (z : k) := by
    exact map_intCast (polynomialFunctionPointAlgHom G 1) z
  simp_rw [hcast, hN]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp [N, r]
  · intro σ hσ hne
    suffices (∑ i, (∏ j ∈ Finset.univ.erase i,
        if σ j = i₀ then (0 : k) else if σ j = j then 1 else 0) *
          D (N (σ i) i)) = 0 by
      rw [this, mul_zero]
    apply Finset.sum_eq_zero
    intro i hi
    suffices (∏ j ∈ Finset.univ.erase i,
        if σ j = i₀ then (0 : k) else if σ j = j then 1 else 0) = 0 by
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
          σ.support.card ≤ ({i} : Finset (Fin n)).card :=
            Finset.card_le_card hsupport
          _ = 1 := Finset.card_singleton i
      exact hne (Equiv.Perm.card_support_le_one.mp hcard)
    obtain ⟨j, hji, hj⟩ := hmoved
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    by_cases hrow : σ j = i₀ <;> simp [hrow, hj]
  · simp

end Theory.AlgebraicGroup.Bor1
