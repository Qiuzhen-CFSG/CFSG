/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinScalar.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.EisensteinRational
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Eisenstein Scalar

The prescribed Hermitian form and its real part are related by scalar rotation. Coordinate identities recover the Hermitian pairing from two real pairings.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinScalar.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators QuadraticAlgebra

abbrev EisensteinRationalCoordinates := Fin 12 → EisensteinRational

/-- The prescribed Hermitian form, including the factor 2/9. -/
def eisensteinHermitian (z w : EisensteinRationalCoordinates) : EisensteinRational :=
  (2/9 : ℚ) • ∑ i, star (z i) * w i

def eisensteinBilinear (z w : EisensteinRationalCoordinates) : ℚ :=
  eisensteinReal (eisensteinHermitian z w)

def eisensteinRotation (z : EisensteinRationalCoordinates) : EisensteinRationalCoordinates :=
  fun i => rationalOmega * z i

theorem eisensteinRotation_polynomial (z : EisensteinRationalCoordinates) :
    eisensteinRotation (eisensteinRotation z) + eisensteinRotation z + z = 0 := by
  funext i
  have h := congrArg (fun a : EisensteinRational => a*z i) rationalOmega_relation
  simpa [eisensteinRotation, pow_two, add_mul, mul_assoc] using h

theorem eisensteinRotation_cube (z : EisensteinRationalCoordinates) :
    eisensteinRotation (eisensteinRotation (eisensteinRotation z)) = z := by
  funext i
  have h := congrArg (fun a : EisensteinRational => a*z i) rationalOmega_cube
  simpa [eisensteinRotation, pow_succ, mul_assoc] using h

theorem eisensteinRotation_fixed_iff (z : EisensteinRationalCoordinates) :
    eisensteinRotation z = z ↔ z = 0 := by
  constructor
  · intro h
    funext i
    exact (rationalOmega_fixed_iff (z i)).mp (congrFun h i)
  · rintro rfl; funext i; simp [eisensteinRotation]

theorem eisensteinHermitian_rotation_right (z w : EisensteinRationalCoordinates) :
    eisensteinHermitian z (eisensteinRotation w) = rationalOmega * eisensteinHermitian z w := by
  simp only [eisensteinHermitian, eisensteinRotation, Finset.mul_sum, mul_smul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Commuting with omega and preserving the real form recovers the complete Hermitian form. -/
theorem eisensteinHermitian_of_real_and_rotation
    (f : EisensteinRationalCoordinates → EisensteinRationalCoordinates)
    (hf : ∀ z w, eisensteinBilinear (f z) (f w) = eisensteinBilinear z w)
    (hc : ∀ z, f (eisensteinRotation z) = eisensteinRotation (f z)) :
    ∀ z w, eisensteinHermitian (f z) (f w) = eisensteinHermitian z w := by
  intro z w
  apply eisensteinReal_ext
  · exact hf z w
  · have h := hf z (eisensteinRotation w)
    unfold eisensteinBilinear at h
    rw [hc w, eisensteinHermitian_rotation_right, eisensteinHermitian_rotation_right] at h
    exact h

theorem eisensteinReal_sum {ι : Type*} (s : Finset ι) (f : ι → EisensteinRational) :
    eisensteinReal (∑ i ∈ s, f i) = ∑ i ∈ s, eisensteinReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eisensteinReal]
  | @insert a s ha ih => simp [ha, eisensteinReal_add, ih]

theorem eisensteinBilinear_self (z : EisensteinRationalCoordinates) :
    eisensteinBilinear z z = (2/9 : ℚ) * ∑ i, ((z i).re^2-(z i).re*(z i).im+(z i).im^2) := by
  unfold eisensteinBilinear eisensteinHermitian
  rw [eisensteinReal_smul, eisensteinReal_sum]
  simp only [eisensteinReal_star_mul_self]

theorem eisensteinBilinear_self_nonneg (z : EisensteinRationalCoordinates) :
    0 ≤ eisensteinBilinear z z := by
  unfold eisensteinBilinear eisensteinHermitian
  rw [eisensteinReal_smul, eisensteinReal_sum]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ =>
    eisensteinReal_star_mul_self_nonneg (z i)))

theorem eisensteinBilinear_self_eq_zero (z : EisensteinRationalCoordinates) :
    eisensteinBilinear z z = 0 ↔ z = 0 := by
  unfold eisensteinBilinear eisensteinHermitian
  rw [eisensteinReal_smul, eisensteinReal_sum, mul_eq_zero]
  simp only [show (2/9 : ℚ) ≠ 0 by norm_num, false_or]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => eisensteinReal_star_mul_self_nonneg (z i))]
  simp [eisensteinReal_star_mul_self_eq_zero, funext_iff]

theorem eisensteinScalar_decomposition (a : EisensteinRational)
    (z : EisensteinRationalCoordinates) :
    a • z = a.re • z + a.im • eisensteinRotation z := by
  funext i
  apply QuadraticAlgebra.ext <;>
    simp [eisensteinRotation, rationalOmega, QuadraticAlgebra.omega]; ring

/-- Rational linearity and commutation with the scalar rotation imply K-linearity. -/
theorem eisensteinLinear_of_rotation
    (f : EisensteinRationalCoordinates →ₗ[ℚ] EisensteinRationalCoordinates)
    (hc : ∀ z, f (eisensteinRotation z) = eisensteinRotation (f z))
    (a : EisensteinRational) (z : EisensteinRationalCoordinates) :
    f (a • z) = a • f z := by
  rw [eisensteinScalar_decomposition, map_add, map_smul, map_smul,
    hc, eisensteinScalar_decomposition]

/-- Extension of scalars recovered from an actual commuting rational linear map. -/
def eisensteinLinearOfRotation
    (f : EisensteinRationalCoordinates →ₗ[ℚ] EisensteinRationalCoordinates)
    (hc : ∀ z, f (eisensteinRotation z) = eisensteinRotation (f z)) :
    EisensteinRationalCoordinates →ₗ[EisensteinRational] EisensteinRationalCoordinates where
  toFun := f
  map_add' := f.map_add
  map_smul' := eisensteinLinear_of_rotation f hc

theorem rationalOmega_ne_zero : rationalOmega ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  norm_num [rationalOmega, QuadraticAlgebra.omega] at this

/-- The actual rational scalar rotation as a linear automorphism. -/
noncomputable def eisensteinRotationEquiv :
    EisensteinRationalCoordinates ≃ₗ[ℚ] EisensteinRationalCoordinates :=
  (LinearEquiv.smulOfNeZero EisensteinRational EisensteinRationalCoordinates
    rationalOmega rationalOmega_ne_zero).restrictScalars ℚ

@[simp] theorem eisensteinRotationEquiv_apply (z : EisensteinRationalCoordinates) :
    eisensteinRotationEquiv z = eisensteinRotation z := rfl

theorem eisensteinRotationEquiv_order : orderOf eisensteinRotationEquiv = 3 := by
  apply orderOf_eq_prime
  · apply LinearEquiv.ext
    intro z
    exact eisensteinRotation_cube z
  · intro h
    have he := LinearEquiv.congr_fun h (fun _ => 1)
    have hz := (eisensteinRotation_fixed_iff (fun _ => 1)).mp he
    have hi := congrFun hz 0
    exact one_ne_zero hi

theorem eisensteinRotation_preserves_hermitian (z w : EisensteinRationalCoordinates) :
    eisensteinHermitian (eisensteinRotation z) (eisensteinRotation w) =
      eisensteinHermitian z w := by
  unfold eisensteinHermitian eisensteinRotation
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have ho : star rationalOmega * rationalOmega = 1 := by
    ext <;> norm_num [rationalOmega, QuadraticAlgebra.omega]
  rw [star_mul]
  calc
    star (z i) * star rationalOmega * (rationalOmega * w i) =
        star (z i) * (star rationalOmega * rationalOmega) * w i := by ring
    _ = star (z i) * w i := by rw [ho]; ring

end Atlas.Lattices
