module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.RestrictedAdjoint.Support
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.Cartan

/-!
# Positive adjoint transport on short inputs

On a short input coordinate, the second divided power is either zero or the
single column carrying the negative simple root to the positive simple root.
Its adjoint image is consequently zero or the simple root operator, whose
product with the second divided power vanishes. This proves degree four.
Degree three follows from degrees one and two using invariance of short support
under the first divided power. Thus the only remaining premises are the first
two root coefficients on geometrically short roots.

The matrices are the actual Geck divided powers; their two-step column formula
is proved in `Intertwining.Simple.LowDegrees`. No full adjoint equivariance is
assumed or required here.
-/

@[expose] public section

open scoped Classical Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup

namespace ReeF4.WordRelations.Faithfulness.RestrictedAdjoint

open Adjoint Adjoint.PositiveSimple

/-- Adjoint transport only on vectors in the short-coordinate ideal. -/
def EquivariantOnShort (m : ℕ)
    (g : (Matrix Coordinate Coordinate (CoefficientField m))ˣ) : Prop :=
  ∀ v, ShortSupported v →
    adjointMap m ((g : Matrix Coordinate Coordinate (CoefficientField m)) *ᵥ v) * g =
      g * adjointMap m v

theorem equivariantOnShort_iff_basis (m : ℕ)
    (g : (Matrix Coordinate Coordinate (CoefficientField m))ˣ) :
    EquivariantOnShort m g ↔ ∀ j, IsShortCoordinate j →
      adjointMap m ((g : Matrix Coordinate Coordinate (CoefficientField m)) *ᵥ Pi.single j 1) * g =
        g * adjointMap m (Pi.single j 1) := by
  constructor
  · intro h j hj
    exact h _ (shortSupported_single j hj)
  · intro h v hv
    have he : v = ∑ j, v j • Pi.single j 1 := by
      ext k
      simp [Pi.single_apply, smul_eq_mul]
    rw [he]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_sum, map_smul,
      Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : IsShortCoordinate j
    · exact congrArg (fun A => v j • A) (h j hj)
    · simp only [hv j hj, zero_smul]

theorem columnImage_two_short (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) (hj : IsShortCoordinate j) :
    letI := typeF4RootPairing.indexNeg
    columnImage m i 2 j =
      if j = Sum.inr (-i.val) then dividedPower m i 1 else 0 := by
  let := typeF4RootPairing.indexNeg
  have hcol : (fun k => dividedPower m i 2 k j) =
      if j = Sum.inr (-i.val) then Pi.single (Sum.inr i.val) 1 else 0 := by
    ext k
    change specializeMatrix (S := CoefficientField m)
      (eDividedPower (P := typeF4RootPairing) i 2) k j = _
    rw [specialize_eDividedPower_two_apply i k j (Or.inr hj)]
    change (if k = Sum.inr i.val ∧ j = Sum.inr (-i.val) then (1 : CoefficientField m) else 0) =
      (if j = Sum.inr (-i.val) then
        (Pi.single (Sum.inr i.val) 1 : Coordinate → CoefficientField m) else 0) k
    by_cases h : j = Sum.inr (-i.val)
    · simp only [h, and_true, if_true, Pi.single_apply]
    · simp only [h, and_false, if_false, Pi.zero_apply]
  rw [columnImage, hcol]
  split_ifs
  · rw [adjointMap_single, coordinateOperator_simple]
  · exact map_zero _

/-- The quartic coefficient vanishes unconditionally on the short coordinates. -/
theorem coefficientIdentity_four_short (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) (hj : IsShortCoordinate j) : CoefficientIdentity m i j 4 := by
  let := typeF4RootPairing.indexNeg
  simp only [CoefficientIdentity, curveProductCoefficient, columnImage_three_eq_zero,
    dividedPower_three_eq_zero, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
    dividedPower_eq_zero m i 4 (by omega)]
  rw [columnImage_two_short m i j hj]
  split_ifs
  · rw [dividedPower_mul, dividedPower_three_eq_zero, smul_zero]
  · exact zero_mul _

private theorem degree_two_linear_short (m : ℕ) (i : typeF4RootPairing_base.support)
    (h : ∀ j, IsShortCoordinate j → CoefficientIdentity m i j 2)
    (v : Coordinate → CoefficientField m) (hv : ShortSupported v) :
    adjointMap m (dividedPower m i 2 *ᵥ v) +
      adjointMap m (dividedPower m i 1 *ᵥ v) * dividedPower m i 1 +
      adjointMap m v * dividedPower m i 2 =
        dividedPower m i 2 * adjointMap m v := by
  have he : v = ∑ j, v j • Pi.single j 1 := by
    ext k
    simp [Pi.single_apply, smul_eq_mul]
  rw [he]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_sum, map_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    ← Finset.sum_add_distrib, ← smul_add]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : IsShortCoordinate j
  · have hc := h j hj
    unfold CoefficientIdentity curveProductCoefficient at hc
    simpa only [Matrix.mulVec_single_one, adjointMap_single, columnImage,
      Matrix.col_apply'] using congrArg (fun A => v j • A) hc
  · simp only [hv j hj, zero_smul]

/-- Only short-coordinate degree-two identities are used in the cubic argument. -/
theorem coefficientIdentity_three_short (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) (hj : IsShortCoordinate j) (h1 : CoefficientIdentity m i j 1)
    (h2 : ∀ k, IsShortCoordinate k → CoefficientIdentity m i k 2) :
    CoefficientIdentity m i j 3 := by
  let E := dividedPower m i 1
  let B := dividedPower m i 2
  let A := coordinateOperator m j
  let U := columnImage m i 1 j
  let V := columnImage m i 2 j
  have hEE : E * E = 0 := by
    have h := dividedPower_mul m i 1 1
    rw [← Nat.cast_smul_eq_nsmul (CoefficientField m)] at h
    change E * E = (2 : CoefficientField m) • B at h
    simpa only [CharTwo.two_eq_zero, zero_smul] using h
  have hBE : B * E = 0 := by
    change dividedPower m i 2 * dividedPower m i 1 = 0
    rw [dividedPower_mul, dividedPower_three_eq_zero, smul_zero]
  have hUB : U * B = B * U := by
    have h := degree_two_linear_short m i h2 (E *ᵥ Pi.single j 1)
      (shortSupported_dividedPower_one m i (shortSupported_single j hj))
    change adjointMap m (B *ᵥ (E *ᵥ Pi.single j 1)) +
      adjointMap m (E *ᵥ (E *ᵥ Pi.single j 1)) * E +
      adjointMap m (E *ᵥ Pi.single j 1) * B = B * adjointMap m (E *ᵥ Pi.single j 1) at h
    simp only [Matrix.mulVec_mulVec, hEE, hBE, Matrix.zero_mulVec, map_zero,
      Matrix.zero_mul, zero_add] at h
    simpa only [Matrix.mulVec_single_one, U, columnImage, E, Matrix.col_apply'] using h
  have h2j := h2 j hj
  change V + U * E + A * B = B * A at h2j
  change U + A * E = E * A at h1
  have hVE : V * E = B * A * E := by
    have h := congrArg (fun Z => Z * E) h2j
    simpa only [Matrix.add_mul, mul_assoc, hEE, hBE, Matrix.mul_zero, add_zero] using h
  have hBU : B * U + B * A * E = 0 := by
    have h := congrArg (fun Z => B * Z) h1
    simpa only [Matrix.mul_add, ← mul_assoc, hBE, Matrix.zero_mul] using h
  simp only [CoefficientIdentity, curveProductCoefficient, columnImage_three_eq_zero,
    dividedPower_three_eq_zero, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  change V * E + U * B = 0
  rw [hVE, hUB, add_comm]
  exact hBU

/-- Positive simple transport needs exactly degrees one and two on short roots. -/
theorem positive_equivariantOnShort_of_coefficients
    (m : ℕ) (i : typeF4RootPairing_base.support) (t : CoefficientField m)
    (h1 : ∀ r : typeF4Roots, IsShortRoot r → CoefficientIdentity m i (Sum.inr r) 1)
    (h2 : ∀ r : typeF4Roots, IsShortRoot r → CoefficientIdentity m i (Sum.inr r) 2) :
    EquivariantOnShort m (positiveUnit i t) := by
  apply (equivariantOnShort_iff_basis m _).mpr
  rintro (j | r) hj
  · exact positive_cartan_basis m i j t
  · apply basis_of_quadratic_coefficients m i (Sum.inr r) t
    intro d hd1 hd4
    interval_cases d
    · exact h1 r hj
    · exact h2 r hj
    · apply coefficientIdentity_three_short m i (Sum.inr r) hj (h1 r hj)
      rintro (k | s) hk
      · exact coefficientIdentity_cartan m i k 2 (by omega) (by omega)
      · exact h2 s hk
    · exact coefficientIdentity_four_short m i (Sum.inr r) hj

end ReeF4.WordRelations.Faithfulness.RestrictedAdjoint
