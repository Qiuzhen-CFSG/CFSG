module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# Cyclic intertwiners for two-dimensional matrices

Over any field, two nonscalar two-dimensional matrices with the same trace
and determinant are intertwined by an invertible matrix. A cyclic vector
gives the basis (v,Av), in which the matrix is [[0,-detA],[1,traceA]].
The two basis changes therefore give the desired intertwiner.

This is the GL2 part of the SL2 p-regular trace-class classification.
The separate centralizer-determinant theorem supplies the determinant-one
adjustment; this theorem does not assert it without that additional step.
-/

namespace Matrix
variable {K : Type*} [Field K]

private theorem exists_cyclic_vector (A : Matrix (Fin 2) (Fin 2) K)
    (hA : ¬ ∃ a : K, A = a • 1) :
    ∃ x y : K, x * (A 1 0 * x + A 1 1 * y) -
      y * (A 0 0 * x + A 0 1 * y) ≠ 0 := by
  by_cases hc : A 1 0 = 0
  · by_cases hb : A 0 1 = 0
    · have had : A 0 0 ≠ A 1 1 := by
        intro h
        apply hA
        refine ⟨A 0 0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc, h]
      exact ⟨1, 1, by simpa [hc, hb, sub_ne_zero] using had.symm⟩
    · exact ⟨0, 1, by simpa using hb⟩
  · exact ⟨1, 0, by simpa using hc⟩

private theorem exists_companion_basis (A : Matrix (Fin 2) (Fin 2) K)
    (hA : ¬ ∃ a : K, A = a • 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) K, det P ≠ 0 ∧
      A * P = P * !![0, -det A; 1, trace A] := by
  obtain ⟨x, y, hxy⟩ := exists_cyclic_vector A hA
  refine ⟨!![x, A 0 0 * x + A 0 1 * y; y, A 1 0 * x + A 1 1 * y], ?_, ?_⟩
  · simpa [det_fin_two, mul_comm] using hxy
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, det_fin_two, trace_fin_two] <;> ring

public theorem exists_intertwiner_of_trace_eq_det_eq
    (A B : Matrix (Fin 2) (Fin 2) K)
    (hA : ¬ ∃ a : K, A = a • 1) (hB : ¬ ∃ b : K, B = b • 1)
    (ht : trace A = trace B) (hd : det A = det B) :
    ∃ D : Matrix (Fin 2) (Fin 2) K, det D ≠ 0 ∧ A * D = D * B := by
  obtain ⟨P, hP, hAP⟩ := exists_companion_basis A hA
  obtain ⟨Q, hQ, hBQ⟩ := exists_companion_basis B hB
  have hQi : IsUnit (det Q) := isUnit_iff_ne_zero.mpr hQ
  have hQinv : det Q⁻¹ ≠ 0 := (Q.isUnit_nonsing_inv_det hQi).ne_zero
  have hJQ : (!![0, -det B; 1, trace B]) * Q⁻¹ = Q⁻¹ * B := by
    have hj : Q⁻¹ * B * Q = !![0, -det B; 1, trace B] := by
      rw [Matrix.mul_assoc, hBQ, ← Matrix.mul_assoc, Q.nonsing_inv_mul hQi,
        Matrix.one_mul]
    rw [← hj, Q.mul_nonsing_inv_cancel_right _ hQi]
  refine ⟨P * Q⁻¹, by rw [det_mul]; exact mul_ne_zero hP hQinv, ?_⟩
  calc
    A * (P * Q⁻¹) = (A * P) * Q⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = (P * !![0, -det B; 1, trace B]) * Q⁻¹ := by rw [hAP, ht, hd]
    _ = P * (Q⁻¹ * B) := by rw [Matrix.mul_assoc, hJQ]
    _ = (P * Q⁻¹) * B := (Matrix.mul_assoc _ _ _).symm

end Matrix
