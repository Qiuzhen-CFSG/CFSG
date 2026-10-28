module
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4IntegralChevalleyRepresentation
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.Coordinates
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.RootGeometry

/-!
# Cubic vanishing and opposition for the F4 simple curves

The canonical all-root routes are empty on the chosen base, so the actual F4
root-curve coefficients there are Geck's positive and negative divided powers.
The cubic coefficient vanishes by the Euclidean root-length bound. Opposition
commutes with the quotient-to-ideal coordinate map, and hence transports every
positive coefficient comparison to its negative counterpart.

The representation is the integral construction in
`F4IntegralChevalleyRepresentation`; the exceptional-root convention is that
of `RootDuality` (Aschbacher–Smith, Remark A.2.4).
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Classical Matrix
namespace ReeF4.WordRelations

lemma eDividedPower_three (i : typeF4RootPairing_base.support) :
    eDividedPower (P := typeF4RootPairing) i 3 = 0 := by
  ext (j | j) (k | k)
  · rfl
  · rfl
  · rfl
  · exact if_neg (root_ne_add_three_nsmul i k j)

lemma fDividedPower_three (i : typeF4RootPairing_base.support) :
    fDividedPower (P := typeF4RootPairing) i 3 = 0 := by
  simp only [fDividedPower, eDividedPower_three, Matrix.mul_zero, Matrix.zero_mul]

lemma rootDividedPower_simple (i : typeF4RootPairing_base.support) (n : ℕ) :
    Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootDividedPower i n =
      eDividedPower (P := typeF4RootPairing) i n := by
  change rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base) i n = _
  rw [rootDividedPower_of_pos _ (typeF4RootPairing_base.isPos_of_mem_support i.property),
    rootRoute_word_simple, rootRoute_simple, transportedMatrix_nil]

lemma rootDividedPower_neg_simple (i : typeF4RootPairing_base.support) (n : ℕ) :
    let := typeF4RootPairing.indexNeg
    Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootDividedPower (-i : typeF4Roots) n =
      fDividedPower (P := typeF4RootPairing) i n := by
  let := typeF4RootPairing.indexNeg
  change rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base)
    (-i : typeF4Roots) n = _
  rw [rootDividedPower_neg_of_pos _ (typeF4RootPairing_base.isPos_of_mem_support i.property),
    rootRoute_word_simple, rootRoute_simple, transportedMatrix_nil]

lemma omegaMatrix_apply (i j : Coordinate) :
    omegaMatrix (P := typeF4RootPairing) (b := typeF4RootPairing_base) i j =
      if i = coordinateOpposition j then 1 else 0 := by
  let := typeF4RootPairing.indexNeg
  rcases i with i | i <;> rcases j with j | j <;>
    simp [omegaMatrix, Matrix.one_apply]

lemma specialize_omegaMatrix_mul {K : Type*} [Ring K]
    (A : Matrix Coordinate Coordinate K) (i j : Coordinate) :
    (specializeMatrix (S := K) (omegaMatrix (P := typeF4RootPairing) (b := typeF4RootPairing_base)) * A) i j =
      A (coordinateOpposition i) j := by
  have heq (k : Coordinate) : i = coordinateOpposition k ↔ k = coordinateOpposition i := by
    constructor
    · intro h
      rw [h, coordinateOpposition_involutive k]
    · intro h
      rw [h, coordinateOpposition_involutive i]
  simp [Matrix.mul_apply, specializeMatrix, omegaMatrix_apply, heq]

lemma mul_specialize_omegaMatrix {K : Type*} [Ring K]
    (A : Matrix Coordinate Coordinate K) (i j : Coordinate) :
    (A * specializeMatrix (S := K) (omegaMatrix (P := typeF4RootPairing) (b := typeF4RootPairing_base))) i j =
      A i (coordinateOpposition j) := by
  simp [Matrix.mul_apply, specializeMatrix, omegaMatrix_apply]

lemma quotientToIdeal_commute_omegaMatrix {K : Type*} [Ring K] :
    quotientToIdeal (K := K) * specializeMatrix (S := K) (omegaMatrix
      (P := typeF4RootPairing) (b := typeF4RootPairing_base)) =
    specializeMatrix (S := K) (omegaMatrix (P := typeF4RootPairing)
      (b := typeF4RootPairing_base)) * quotientToIdeal := by
  ext i j
  rw [mul_specialize_omegaMatrix, specialize_omegaMatrix_mul]
  simpa only [coordinateOpposition_involutive j] using
    (quotientToIdeal_opposition (K := K) i (coordinateOpposition j)).symm

lemma rootDividedPower_three (r : typeF4Roots) :
    Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootDividedPower r 3 = 0 := by
  change rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base) r 3 = 0
  simp only [rootDividedPower]
  split <;> simp only [eDividedPower_three, fDividedPower_three,
    transportedMatrix, Matrix.mul_zero, Matrix.zero_mul]

lemma rootCurve_quadratic {K : Type*} [CommRing K] (r : typeF4Roots) (t : K) :
    (Theory.AlgebraicGroup.F4Chevalley.rootCurve r t : Matrix Coordinate Coordinate K) =
      1 + t • specializeMatrix (S := K)
        (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := K)
        (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootDividedPower r 2) := by
  rw [Theory.AlgebraicGroup.F4Chevalley.rootCurve_matrix_formula, rootDividedPower_three,
    specializeMatrix_zero, smul_zero, add_zero]

lemma intertwines_opposition {K : Type*} [Ring K]
    {A B : Matrix Coordinate Coordinate K}
    (h : quotientToIdeal * A = B * quotientToIdeal) :
    quotientToIdeal * (specializeMatrix (S := K) (omegaMatrix
        (P := typeF4RootPairing) (b := typeF4RootPairing_base)) * A *
      specializeMatrix (S := K) (omegaMatrix (P := typeF4RootPairing)
        (b := typeF4RootPairing_base))) =
      (specializeMatrix (S := K) (omegaMatrix (P := typeF4RootPairing)
        (b := typeF4RootPairing_base)) * B *
      specializeMatrix (S := K) (omegaMatrix (P := typeF4RootPairing)
        (b := typeF4RootPairing_base))) * quotientToIdeal := by
  let O := specializeMatrix (S := K) (omegaMatrix (P := typeF4RootPairing)
    (b := typeF4RootPairing_base))
  have hO : quotientToIdeal * O = O * quotientToIdeal := quotientToIdeal_commute_omegaMatrix
  change quotientToIdeal * (O * A * O) = (O * B * O) * quotientToIdeal
  calc
    _ = O * (quotientToIdeal * A) * O := by simp only [← mul_assoc]; rw [hO]
    _ = O * (B * quotientToIdeal) * O := by rw [h]
    _ = _ := by simp only [mul_assoc]; rw [← hO]

lemma negative_coefficients_of_positive {K : Type*} [Ring K]
    (i j : typeF4RootPairing_base.support) (a b : ℕ)
    (h : quotientToIdeal * specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i a) =
      specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) j b) * quotientToIdeal) :
    quotientToIdeal * specializeMatrix (S := K) (fDividedPower (P := typeF4RootPairing) i a) =
      specializeMatrix (S := K) (fDividedPower (P := typeF4RootPairing) j b) * quotientToIdeal := by
  simpa only [fDividedPower, specializeMatrix_mul] using intertwines_opposition h

lemma negative_left_zero_of_positive {K : Type*} [Ring K]
    (i : typeF4RootPairing_base.support) (a : ℕ)
    (h : quotientToIdeal * specializeMatrix (S := K)
      (eDividedPower (P := typeF4RootPairing) i a) = 0) :
    quotientToIdeal * specializeMatrix (S := K)
      (fDividedPower (P := typeF4RootPairing) i a) = 0 := by
  have h' : quotientToIdeal * specializeMatrix (S := K)
      (eDividedPower (P := typeF4RootPairing) i a) = 0 * quotientToIdeal := by
    simpa only [zero_mul] using h
  simpa only [fDividedPower, specializeMatrix_mul, mul_zero, zero_mul] using
    intertwines_opposition h'

lemma negative_right_zero_of_positive {K : Type*} [Ring K]
    (i : typeF4RootPairing_base.support) (a : ℕ)
    (h : specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i a) * quotientToIdeal = 0) :
    specializeMatrix (S := K) (fDividedPower (P := typeF4RootPairing) i a) * quotientToIdeal = 0 := by
  have h' : quotientToIdeal * 0 = specializeMatrix (S := K)
      (eDividedPower (P := typeF4RootPairing) i a) * quotientToIdeal := by
    simpa only [mul_zero] using h.symm
  simpa only [fDividedPower, specializeMatrix_mul, mul_zero, zero_mul] using
    (intertwines_opposition h').symm

end ReeF4.WordRelations
