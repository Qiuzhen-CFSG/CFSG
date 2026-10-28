module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.DeterminantalLocus.Assembly
/-!
# Separate rescaling of two homogeneous coordinate blocks

A polynomial homogeneous for weights `(1,0)` and `(0,1)` scales by the two
corresponding powers. This includes bidegrees with zero components and the zero
polynomial. In particular, normalizing one nonzero coordinate in each block
preserves its zero set. This is the algebraic chart-independence calculation for
the biprojective equations of Borel's flag variety (§11.1).
-/

@[expose] public section
open MvPolynomial
namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus
universe u
variable {k : Type u} [Field k]
private theorem blockWeight_fst {σ τ : Type} [Fintype σ] [Fintype τ]
    (d : (σ ⊕ τ) →₀ ℕ) :
    (Finsupp.weight blockWeight d).1 = ∑ i, d (Sum.inl i) := by
  simp [Finsupp.weight_eq_sum, blockWeight, Fintype.sum_sum_type, Prod.fst_sum]
private theorem blockWeight_snd {σ τ : Type} [Fintype σ] [Fintype τ]
    (d : (σ ⊕ τ) →₀ ℕ) :
    (Finsupp.weight blockWeight d).2 = ∑ i, d (Sum.inr i) := by
  simp [Finsupp.weight_eq_sum, blockWeight, Fintype.sum_sum_type, Prod.snd_sum]

/-- Independent scalar multiplication of the two blocks has the prescribed bidegree. -/
theorem eval_bihomogeneous_scale {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : MvPolynomial (σ ⊕ τ) k) (degree : ℕ × ℕ)
    (hP : P.IsWeightedHomogeneous blockWeight degree)
    (a : σ → k) (b : τ → k) (r s : k) :
    eval (Sum.elim (fun i => r * a i) (fun j => s * b j)) P =
      r ^ degree.1 * s ^ degree.2 * eval (Sum.elim a b) P := by
  classical
  rw [← P.support_sum_monomial_coeff]
  simp only [map_sum, eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have h := hP (mem_support_iff.mp hd)
  have h1 : ∑ i, d (Sum.inl i) = degree.1 := by
    rw [← blockWeight_fst, h]
  have h2 : ∑ i, d (Sum.inr i) = degree.2 := by
    rw [← blockWeight_snd, h]
  simp only [Finsupp.prod_pow, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h1, h2]
  ring

/-- Normalizing a nonzero coordinate in each block preserves vanishing. -/
theorem eval_bihomogeneous_normalize_iff {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : MvPolynomial (σ ⊕ τ) k) (degree : ℕ × ℕ)
    (hP : P.IsWeightedHomogeneous blockWeight degree)
    (a : σ → k) (b : τ → k) (i : σ) (j : τ) (hi : a i ≠ 0) (hj : b j ≠ 0) :
    eval (Sum.elim (fun l => (a i)⁻¹ * a l) (fun l => (b j)⁻¹ * b l)) P = 0 ↔
      eval (Sum.elim a b) P = 0 := by
  rw [eval_bihomogeneous_scale P degree hP]
  simp [hi, hj]
end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus
