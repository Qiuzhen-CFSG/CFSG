module
public import Mathlib.Analysis.Matrix.Order

/-!
# Nonnegative contraction of positive semidefinite matrices

The sum of entrywise products of two real positive semidefinite matrices is
nonnegative. The Schur product theorem makes their entrywise product positive
semidefinite; evaluate its quadratic form on the all-ones vector.

This elementary contraction is the algebraic comparison behind Dirichlet
energy under a decrease of the target metric, as used in Colding–Minicozzi
§1.1, equation (1.2). Neither matrix needs to be invertible.
-/

namespace Matrix
variable {ι : Type*} [Fintype ι]
public theorem PosSemidef.sum_mul_nonneg {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ∑ i, ∑ j, A i j * B i j := by
  simpa [Matrix.mulVec, dotProduct, Matrix.hadamard_apply] using
    (hA.hadamard hB).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
end Matrix
