module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Trace bounded by the inverse-metric tensor norm

For a real positive-semidefinite matrix `G` and any covariant two-tensor `R`,
the square of the contraction of `R` with `G⁻¹` is at most the dimension times
its squared tensor norm, computed using two copies of `G⁻¹`. No symmetry
hypothesis on `R` is required. This is the finite-dimensional algebra behind
the scalar-curvature estimate in BBBMP, Appendix C.2, Proposition C.2.1.

The Kronecker product `G⁻¹ ⊗ G⁻¹` defines a positive-semidefinite pairing on
matrix entries. Cauchy–Schwarz for this pairing is proved from the discriminant
of its nonnegative quadratic polynomial. Pairing `R` with `G` gives the trace,
and pairing `G` with itself gives the dimension by the inverse identities.
The singular case is included: Mathlib's nonsingular inverse is then zero.
-/

open scoped BigOperators Kronecker
namespace Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
private theorem weighted_cauchy_schwarz (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (u v : ι → ℝ) :
    ((A *ᵥ v) ⬝ᵥ u) ^ 2 ≤ ((A *ᵥ u) ⬝ᵥ u) * ((A *ᵥ v) ⬝ᵥ v) := by
  have hsym : (A *ᵥ u) ⬝ᵥ v = (A *ᵥ v) ⬝ᵥ u := by
    rw [dotProduct_comm, dotProduct_mulVec]
    have ha : A.transpose = A := by simpa using hA.isHermitian.eq
    rw [← mulVec_transpose, ha]
  have hpoly (t : ℝ) : 0 ≤ ((A *ᵥ u) ⬝ᵥ u) * (t * t) +
      2 * ((A *ᵥ v) ⬝ᵥ u) * t + ((A *ᵥ v) ⬝ᵥ v) := by
    have hp := hA.dotProduct_mulVec_nonneg (t • u + v)
    simp only [star_trivial, mulVec_add, mulVec_smul, dotProduct_add,
      add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hp
    simp_rw [dotProduct_comm u, dotProduct_comm v, hsym] at hp
    nlinarith
  have hd := discrim_le_zero hpoly
  dsimp [discrim] at hd
  nlinarith

private theorem kronecker_mulVec_metric (G : Matrix ι ι ℝ) (hG : G.IsHermitian)
    (hunit : IsUnit G.det) :
    (G⁻¹ ⊗ₖ G⁻¹) *ᵥ (fun p : ι × ι => G p.1 p.2) =
      (fun p : ι × ι => G⁻¹ p.1 p.2) := by
  funext ⟨i, j⟩
  simp only [mulVec, dotProduct, kronecker_apply, Fintype.sum_prod_type]
  calc
    ∑ k, ∑ l, G⁻¹ i k * G⁻¹ j l * G k l =
        ∑ k, G⁻¹ i k * (∑ l, G k l * G⁻¹ l j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      have hs : G⁻¹ j l = G⁻¹ l j := by
        have h := congrFun (congrFun hG.inv.eq j) l
        simpa using h.symm
      rw [hs]
      ring
    _ = G⁻¹ i j := by
      have hmul := G.mul_nonsing_inv hunit
      simp_rw [← mul_apply, hmul]
      simp

/-- The squared inverse-metric trace of any real two-tensor is bounded by the
index cardinality times its squared inverse-metric tensor norm. -/
public theorem trace_contraction_sq_le (G R : Matrix ι ι ℝ) (hG : G.PosSemidef) :
    (∑ i, ∑ j, G⁻¹ i j * R i j) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, ∑ j, ∑ k, ∑ l,
        G⁻¹ i k * G⁻¹ j l * R i j * R k l := by
  by_cases hunit : IsUnit G.det
  · let A := G⁻¹ ⊗ₖ G⁻¹
    let r : ι × ι → ℝ := fun p => R p.1 p.2
    let g : ι × ι → ℝ := fun p => G p.1 p.2
    have hAg : A *ᵥ g = fun p => G⁻¹ p.1 p.2 :=
      kronecker_mulVec_metric G hG.isHermitian hunit
    have hgg : (A *ᵥ g) ⬝ᵥ g = (Fintype.card ι : ℝ) := by
      rw [hAg]
      simp only [dotProduct, Fintype.sum_prod_type, g]
      have hs (i j : ι) : G i j = G j i := by
        have h := congrFun (congrFun hG.isHermitian.eq i) j
        simpa using h.symm
      calc
        ∑ i, ∑ j, G⁻¹ i j * G i j = ∑ i, (G⁻¹ * G) i i := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [mul_apply]
          apply Finset.sum_congr rfl
          intro j _
          rw [hs i j]
        _ = _ := by rw [G.nonsing_inv_mul hunit]; simp
    have hcs := weighted_cauchy_schwarz A (hG.inv.kronecker hG.inv) r g
    rw [hgg, hAg] at hcs
    simp only [dotProduct, Fintype.sum_prod_type, r] at hcs
    rw [mul_comm] at hcs
    convert hcs using 1
    congr 1
    simp only [A, mulVec, dotProduct, Fintype.sum_prod_type, kronecker_apply,
      Finset.sum_mul]
    congr 1
    ext i
    congr 1
    ext j
    congr 1
    ext k
    congr 1
    ext l
    ring
  · rw [nonsing_inv_apply_not_isUnit G hunit]
    simp

end
end Matrix
