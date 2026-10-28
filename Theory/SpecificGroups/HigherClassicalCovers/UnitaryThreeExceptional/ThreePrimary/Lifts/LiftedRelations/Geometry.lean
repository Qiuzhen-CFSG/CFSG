module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.FiniteRelations
import Mathlib.Tactic.FinCases

/-!
# Normalizers of the six marked unitary roots

The sign torus fixes the two long roots. A determinant-one permutation swaps
those roots, and a monomial unitary matrix moves the first short-root plane to
the middle short-root plane. The second published torus rotates both short
planes and inverts the long roots. All identities are checked before projection
and then passed through the original `coordinateProjection`.

These are local inputs to the exceptional three-part calculation for
Aschbacher--Smith I.1.4(5), printed p.408; GLS3 §6.1. No covering or multiplier
statement is assumed in the matrix calculations.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
namespace LiftedRelations

theorem torus_fixes_long (r : Fin 6) (hr : r = 2 ∨ r = 5) :
    Commute (torus 0) (root r) := by
  apply Commute.map _ coordinateProjection
  apply Subtype.ext
  apply Units.ext
  change torusMatrix 0 * rootMatrix r = rootMatrix r * torusMatrix 0
  rcases hr with rfl | rfl <;> decide +kernel

/-- The second torus permutes the marked root lines. -/
def rotatedRoot : Fin 6 → Fin 6 := ![1, 0, 2, 4, 3, 5]

/-- The exponent records the sign on each rotated root. -/
def rotationPower : Fin 6 → ℕ := ![2, 1, 2, 1, 2, 2]

theorem torus_rotates (r : Fin 6) :
    torus 1 * root r * (torus 1)⁻¹ = root (rotatedRoot r) ^ rotationPower r := by
  have h : torusSU 1 * rootSU r = rootSU (rotatedRoot r) ^ rotationPower r * torusSU 1 := by
    apply Subtype.ext
    apply Units.ext
    change torusMatrix 1 * rootMatrix r =
      rootMatrix (rotatedRoot r) ^ rotationPower r * torusMatrix 1
    fin_cases r <;> decide +kernel
  have hh := congrArg coordinateProjection ((mul_inv_eq_iff_eq_mul).mpr h)
  simpa only [map_mul, map_inv, map_pow, root, torus] using hh

theorem torus_commute (i j : Fin 2) : Commute (torus i) (torus j) := by
  apply Commute.map _ coordinateProjection
  apply Subtype.ext
  apply Units.ext
  change torusMatrix i * torusMatrix j = torusMatrix j * torusMatrix i
  fin_cases i <;> fin_cases j <;> decide +kernel

private def longSwapMatrix : Mat := !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]
private def longSwapGL : GL (Fin 4) K :=
  ⟨longSwapMatrix, longSwapMatrix, by decide +kernel, by decide +kernel⟩
private def longSwapSU : CoordinateSU := ⟨longSwapGL, by
  rw [coordinateForm.mem_specialSubgroup_iff]
  constructor
  · change coordinateForm.conjTranspose longSwapMatrix * coordinateForm.form * longSwapMatrix = _
    decide +kernel
  · apply Units.ext
    change longSwapMatrix.det = 1
    decide +kernel⟩

/-- A simultaneous swap of the hyperbolic coordinates exchanges the long roots. -/
theorem exists_long_swap : ∃ t : S,
    t * root 2 * t⁻¹ = root 5 ∧ t * root 5 * t⁻¹ = root 2 := by
  refine ⟨coordinateProjection longSwapSU, ?_, ?_⟩
  · have h : longSwapSU * rootSU 2 = rootSU 5 * longSwapSU := by
      apply Subtype.ext
      apply Units.ext
      change longSwapMatrix * rootMatrix 2 = rootMatrix 5 * longSwapMatrix
      decide +kernel
    simpa only [map_mul, map_inv, root] using
      congrArg coordinateProjection ((mul_inv_eq_iff_eq_mul).mpr h)
  · have h : longSwapSU * rootSU 5 = rootSU 2 * longSwapSU := by
      apply Subtype.ext
      apply Units.ext
      change longSwapMatrix * rootMatrix 5 = rootMatrix 2 * longSwapMatrix
      decide +kernel
    simpa only [map_mul, map_inv, root] using
      congrArg coordinateProjection ((mul_inv_eq_iff_eq_mul).mpr h)

private def shortMoveMatrix : Mat :=
  !![1,0,0,0; 0,0,imaginary,0; 0,imaginary,0,0; 0,0,0,1]
private def shortMoveInverse : Mat :=
  !![1,0,0,0; 0,0,-imaginary,0; 0,-imaginary,0,0; 0,0,0,1]
private def shortMoveGL : GL (Fin 4) K :=
  ⟨shortMoveMatrix, shortMoveInverse, by decide +kernel, by decide +kernel⟩
private def shortMoveSU : CoordinateSU := ⟨shortMoveGL, by
  rw [coordinateForm.mem_specialSubgroup_iff]
  constructor
  · change coordinateForm.conjTranspose shortMoveMatrix * coordinateForm.form * shortMoveMatrix = _
    decide +kernel
  · apply Units.ext
    change shortMoveMatrix.det = 1
    decide +kernel⟩

/-- The two short-root planes are related inside the actual special unitary group. -/
theorem exists_short_move : ∃ t : S,
    t * root 0 * t⁻¹ = root 4 ^ 2 ∧ t * root 1 * t⁻¹ = root 3 := by
  refine ⟨coordinateProjection shortMoveSU, ?_, ?_⟩
  · have h : shortMoveSU * rootSU 0 = rootSU 4 ^ 2 * shortMoveSU := by
      apply Subtype.ext
      apply Units.ext
      change shortMoveMatrix * rootMatrix 0 = rootMatrix 4 ^ 2 * shortMoveMatrix
      decide +kernel
    simpa only [map_mul, map_inv, map_pow, root] using
      congrArg coordinateProjection ((mul_inv_eq_iff_eq_mul).mpr h)
  · have h : shortMoveSU * rootSU 1 = rootSU 3 * shortMoveSU := by
      apply Subtype.ext
      apply Units.ext
      change shortMoveMatrix * rootMatrix 1 = rootMatrix 3 * shortMoveMatrix
      decide +kernel
    simpa only [map_mul, map_inv, root] using
      congrArg coordinateProjection ((mul_inv_eq_iff_eq_mul).mpr h)

end LiftedRelations
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
