/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinShortGeometry.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinScalar

/-!
# Eisenstein Short Geometry

Three phase-separated differences have mean norm equal to the sum of the original norms. This identity gives a norm bound, and equality forces Hermitian orthogonality.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinShortGeometry.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators QuadraticAlgebra

theorem eisensteinBilinear_add_left (x y z : EisensteinRationalCoordinates) :
    eisensteinBilinear (x+y) z = eisensteinBilinear x z + eisensteinBilinear y z := by
  simp [eisensteinBilinear, eisensteinHermitian, star_add, add_mul,
    Finset.sum_add_distrib, smul_add, eisensteinReal_add]

theorem eisensteinBilinear_add_right (x y z : EisensteinRationalCoordinates) :
    eisensteinBilinear x (y+z) = eisensteinBilinear x y + eisensteinBilinear x z := by
  simp [eisensteinBilinear, eisensteinHermitian, mul_add,
    Finset.sum_add_distrib, smul_add, eisensteinReal_add]

theorem eisensteinBilinear_neg_left (x y : EisensteinRationalCoordinates) :
    eisensteinBilinear (-x) y = -eisensteinBilinear x y := by
  simp [eisensteinBilinear, eisensteinHermitian, eisensteinReal,
    Finset.sum_neg_distrib]
  ring

theorem eisensteinBilinear_neg_right (x y : EisensteinRationalCoordinates) :
    eisensteinBilinear x (-y) = -eisensteinBilinear x y := by
  simp [eisensteinBilinear, eisensteinHermitian, eisensteinReal,
    Finset.sum_neg_distrib]
  ring

theorem eisensteinBilinear_symm (x y : EisensteinRationalCoordinates) :
    eisensteinBilinear x y = eisensteinBilinear y x := by
  unfold eisensteinBilinear eisensteinHermitian
  rw [eisensteinReal_smul, eisensteinReal_smul, eisensteinReal_sum, eisensteinReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [eisensteinReal]
  ring

theorem eisensteinBilinear_sub_self (x y : EisensteinRationalCoordinates) :
    eisensteinBilinear (x-y) (x-y) =
      eisensteinBilinear x x + eisensteinBilinear y y - 2*eisensteinBilinear x y := by
  simp only [sub_eq_add_neg, eisensteinBilinear_add_left, eisensteinBilinear_add_right,
    eisensteinBilinear_neg_left, eisensteinBilinear_neg_right]
  rw [eisensteinBilinear_symm y x]
  ring

theorem eisensteinBilinear_rotation_self (x : EisensteinRationalCoordinates) :
    eisensteinBilinear (eisensteinRotation x) (eisensteinRotation x) =
      eisensteinBilinear x x := by
  unfold eisensteinBilinear
  rw [eisensteinRotation_preserves_hermitian]

theorem eisensteinBilinear_rotation_sum (x y : EisensteinRationalCoordinates) :
    eisensteinBilinear x y + eisensteinBilinear x (eisensteinRotation y) +
      eisensteinBilinear x (eisensteinRotation (eisensteinRotation y)) = 0 := by
  have h := congrArg (eisensteinBilinear x) (eisensteinRotation_polynomial y)
  simp only [eisensteinBilinear_add_right] at h
  have hz : eisensteinBilinear x 0 = 0 := by simp [eisensteinBilinear, eisensteinHermitian, eisensteinReal]
  rw [hz] at h
  linarith

/-- Three phase-separated differences have mean norm equal to the sum of
the two original norms. -/
theorem eisenstein_three_difference_norms (x y : EisensteinRationalCoordinates) :
    eisensteinBilinear (x-y) (x-y) +
      eisensteinBilinear (x-eisensteinRotation y) (x-eisensteinRotation y) +
      eisensteinBilinear (x-eisensteinRotation (eisensteinRotation y))
        (x-eisensteinRotation (eisensteinRotation y)) =
      3*(eisensteinBilinear x x + eisensteinBilinear y y) := by
  simp only [eisensteinBilinear_sub_self, eisensteinBilinear_rotation_self]
  linarith [eisensteinBilinear_rotation_sum x y]

/-- A common lower bound for the three phase differences bounds the sum of norms. -/
theorem eisenstein_norm_sum_ge_of_three_differences
    (x y : EisensteinRationalCoordinates) (b : ℚ)
    (h0 : b ≤ eisensteinBilinear (x-y) (x-y))
    (h1 : b ≤ eisensteinBilinear (x-eisensteinRotation y) (x-eisensteinRotation y))
    (h2 : b ≤ eisensteinBilinear (x-eisensteinRotation (eisensteinRotation y))
      (x-eisensteinRotation (eisensteinRotation y))) :
    b ≤ eisensteinBilinear x x + eisensteinBilinear y y := by
  linarith [eisenstein_three_difference_norms x y]

/-- At equality in the three-difference bound, the two vectors are Hermitian orthogonal. -/
theorem eisenstein_hermitian_zero_of_three_differences
    (x y : EisensteinRationalCoordinates) (b : ℚ)
    (h0 : b ≤ eisensteinBilinear (x-y) (x-y))
    (h1 : b ≤ eisensteinBilinear (x-eisensteinRotation y) (x-eisensteinRotation y))
    (h2 : b ≤ eisensteinBilinear (x-eisensteinRotation (eisensteinRotation y))
      (x-eisensteinRotation (eisensteinRotation y)))
    (hbound : eisensteinBilinear x x + eisensteinBilinear y y ≤ b) :
    eisensteinHermitian x y = 0 := by
  simp only [eisensteinBilinear_sub_self, eisensteinBilinear_rotation_self] at h0 h1 h2
  have hsum := eisensteinBilinear_rotation_sum x y
  have he0 : eisensteinBilinear x y = 0 := by linarith
  have he1 : eisensteinBilinear x (eisensteinRotation y) = 0 := by linarith
  apply eisensteinReal_ext
  · change eisensteinBilinear x y = eisensteinReal 0
    simpa [eisensteinReal] using he0
  · rw [mul_zero]
    have h := he1
    unfold eisensteinBilinear at h
    rw [eisensteinHermitian_rotation_right] at h
    simpa [eisensteinReal] using h

end Atlas.Lattices
