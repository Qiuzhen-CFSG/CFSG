module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.NegativeSimple
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.Coefficients
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple

/-!
# Invariance of the short-coordinate ideal

The short-coordinate subspace is the kernel of the concrete quotient-to-ideal
map. The proved simple-root intertwining identities therefore make it invariant
under both signs of simple curves. The linear divided powers preserve it as
well, by the corresponding coefficient identities. Opposition preserves root
length and fixes the Cartan coordinates.

These are the invariant-subspace facts needed for restricted adjoint transport
in the characteristic-two F4 representation of Geck's integral construction.
-/

@[expose] public section

open scoped Classical Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup

namespace ReeF4.WordRelations.Faithfulness.RestrictedAdjoint

open Adjoint Adjoint.PositiveSimple

variable {K : Type*} [CommRing K]

/-- Vectors in the short-root ideal, including the two short Cartan coordinates. -/
def ShortSupported (v : Coordinate → K) : Prop :=
  ∀ j, ¬IsShortCoordinate j → v j = 0

theorem shortSupported_single (j : Coordinate) (hj : IsShortCoordinate j) :
    ShortSupported (Pi.single j (1 : K)) := by
  classical
  intro k hk
  have hkj : k ≠ j := by rintro rfl; exact hk hj
  simp [hkj]

theorem quotientToIdeal_mulVec_apply (v : Coordinate → K) (i : Coordinate) :
    (quotientToIdeal *ᵥ v) i =
      if IsShortCoordinate i then v (coordinatePermutation i) else 0 :=
  quotientToIdeal_mul (fun k _ => v k) i i

/-- The kernel convention agrees exactly with support on the geometric short coordinates. -/
theorem shortSupported_iff_kernel (v : Coordinate → K) :
    ShortSupported v ↔ quotientToIdeal *ᵥ v = 0 := by
  classical
  constructor
  · intro hv
    ext i
    rw [quotientToIdeal_mulVec_apply]
    by_cases hi : IsShortCoordinate i
    · rw [if_pos hi]
      exact hv _ (by simpa only [coordinatePermutation_short_iff, not_not] using hi)
    · exact if_neg hi
  · intro hv j hj
    have h := congrFun hv (coordinatePermutation j)
    simpa only [quotientToIdeal_mulVec_apply,
      if_pos ((coordinatePermutation_short_iff j).mpr hj),
      coordinatePermutation_involutive j, Pi.zero_apply] using h

theorem shortSupported_mulVec_of_intertwines
    (A B : Matrix Coordinate Coordinate K)
    (h : quotientToIdeal * A = B * quotientToIdeal)
    {v : Coordinate → K} (hv : ShortSupported v) : ShortSupported (A *ᵥ v) := by
  rw [shortSupported_iff_kernel] at hv ⊢
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem shortSupported_positive (i : typeF4RootPairing_base.support) (t : K)
    [CharP K 2] {v : Coordinate → K} (hv : ShortSupported v) :
    ShortSupported ((positiveUnit i t : Matrix Coordinate Coordinate K) *ᵥ v) := by
  rw [← rootCurve_simple]
  exact shortSupported_mulVec_of_intertwines _ _ (intertwines_simple i t) hv

theorem shortSupported_negative (i : typeF4RootPairing_base.support) (t : K)
    [CharP K 2] {v : Coordinate → K} (hv : ShortSupported v) :
    ShortSupported ((negativeUnit i t : Matrix Coordinate Coordinate K) *ᵥ v) := by
  let := typeF4RootPairing.indexNeg
  rw [← rootCurve_neg_simple]
  exact shortSupported_mulVec_of_intertwines _ _ (intertwines_neg_simple i t) hv

theorem shortSupported_dividedPower_one (m : ℕ) (i : typeF4RootPairing_base.support)
    {v : Coordinate → CoefficientField m} (hv : ShortSupported v) :
    ShortSupported (dividedPower m i 1 *ᵥ v) := by
  by_cases hi : IsLongRoot i.val
  · exact shortSupported_mulVec_of_intertwines _ _
      (quotientToIdeal_eDividedPower_one_long i hi) hv
  · rw [shortSupported_iff_kernel, Matrix.mulVec_mulVec]
    change (quotientToIdeal * specializeMatrix (eDividedPower (P := typeF4RootPairing) i 1)) *ᵥ v = 0
    rw [quotientToIdeal_eDividedPower_one_short i hi, Matrix.zero_mulVec]

/-- Basis extension for support preservation, with no assumptions on long columns. -/
theorem shortSupported_mulVec_of_basis (A : Matrix Coordinate Coordinate K)
    (hA : ∀ j, IsShortCoordinate j → ShortSupported (A *ᵥ Pi.single j 1))
    {v : Coordinate → K} (hv : ShortSupported v) : ShortSupported (A *ᵥ v) := by
  classical
  intro k hk
  change ∑ j, A k j * v j = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : IsShortCoordinate j
  · have h := hA j hj k hk
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at h
    rw [h, zero_mul]
  · rw [hv j hj, mul_zero]

theorem shortSupported_omega {v : Coordinate → K} (hv : ShortSupported v) :
    ShortSupported ((omegaUnit (K := K) : Matrix Coordinate Coordinate K) *ᵥ v) := by
  apply shortSupported_mulVec_of_basis _ _ hv
  rintro (j | r) hj
  · rw [omegaUnit_mulVec_cartan]
    exact shortSupported_single _ hj
  · let := typeF4RootPairing.indexNeg
    rw [omegaUnit_mulVec_root]
    exact shortSupported_single _ ((isShortRoot_neg_iff r).mpr hj)

end ReeF4.WordRelations.Faithfulness.RestrictedAdjoint
