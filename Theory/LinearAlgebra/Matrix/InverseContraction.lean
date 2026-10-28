module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Matrix.Order

/-!
# Frame invariance of inverse metric contractions

If a symmetric real bilinear form and a second bilinear form are both
transported by the same invertible matrix, contraction against the inverse
first form is unchanged. The second form need not be symmetric, and the first
need not be nonsingular: the identity also respects the zero convention for
Mathlib's nonsingular inverse.

Write the contraction as a matrix trace. The inverse of a matrix congruence
is a congruence by inverse matrices; cyclicity of trace cancels the change
of frame. This is the algebraic coordinate-independence step for the Dirichlet
energy density in Colding–Minicozzi §1.1, equation (1.2).
-/

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem contraction_eq_trace (G Q : Matrix ι ι ℝ) (hG : G.IsHermitian) :
    (∑ i, ∑ j, G⁻¹ i j * Q i j) = (G⁻¹ * Q).trace := by
  simp only [trace]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs := congrFun (congrFun hG.inv.eq i) j
  simpa using congrArg (fun a => a * Q j i) hs

private theorem trace_inverse_congr (G Q P : Matrix ι ι ℝ) (hP : IsUnit P.det) :
    ((P.transpose * G * P)⁻¹ * (P.transpose * Q * P)).trace = (G⁻¹ * Q).trace := by
  rw [mul_inv_rev, mul_inv_rev]
  have hPt : IsUnit P.transpose.det := by simpa using hP
  calc
    _ = (P⁻¹ * (G⁻¹ * (P.transpose⁻¹ * P.transpose)) * Q * P).trace := by
      simp only [mul_assoc]
    _ = (P⁻¹ * (G⁻¹ * Q) * P).trace := by rw [P.transpose.nonsing_inv_mul hPt]; simp [mul_assoc]
    _ = (P * P⁻¹ * (G⁻¹ * Q)).trace := trace_mul_cycle _ _ _
    _ = _ := by rw [P.mul_nonsing_inv hP, one_mul]

public theorem inverse_contraction_congr (G Q P : Matrix ι ι ℝ)
    (hG : G.IsHermitian) (hP : IsUnit P.det) :
    (∑ i, ∑ j, (P.transpose * G * P)⁻¹ i j * (P.transpose * Q * P) i j) =
      ∑ i, ∑ j, G⁻¹ i j * Q i j := by
  have hGP : (P.transpose * G * P).IsHermitian := by
    simpa using isHermitian_conjTranspose_mul_mul P hG
  rw [contraction_eq_trace _ _ hGP, contraction_eq_trace G Q hG]
  exact trace_inverse_congr G Q P hP
end Matrix
