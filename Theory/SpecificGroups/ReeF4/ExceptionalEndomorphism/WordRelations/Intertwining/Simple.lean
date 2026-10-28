module
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.LowDegrees
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.LongLinear
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.ShortQuadratic
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.PolynomialReduction
public import Theory.SpecificGroups.ReeF4.Field

/-!
# Simple-root assembly for the exceptional F4 intertwiner

The quotient-to-ideal matrix intertwines the actual positive and negative F4
simple-root curves over every commutative ring of characteristic two.
`LongLinear` proves the linear comparison for long simple roots, and
`ShortQuadratic` proves the quadratic-to-linear comparison for short simple roots.
`LowDegrees` proves the other coefficients unconditionally, including odd-term
vanishing on the short-root branch; opposition handles both negative branches.
`PolynomialReduction` then assembles the root-curve polynomials.

The final theorem covers both signs of all four numbered simples over
`CoefficientField m`, including `m = 0`, with no additional coefficient premises.
The parameter is unchanged for geometrically long roots and squared for short
roots, as in `RootDuality`. The divided-power representation is the one in
`F4IntegralChevalleyRepresentation`. This is the simple-root step toward the
exceptional isogeny construction of the Ree family `²F₄` listed in
Aschbacher–Smith, Remark A.2.4 (`refs/quasithin.pdf`).
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup.F4Chevalley
open scoped Classical Matrix
namespace ReeF4.WordRelations

variable {K : Type*} [CommRing K] [CharP K 2]

lemma intertwines_simple_of_coefficients (i : typeF4RootPairing_base.support) (t : K)
    (hlinear : IsLongRoot i.val →
      quotientToIdeal * specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 1) =
        specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) (simplePermutation i) 1) *
          quotientToIdeal)
    (hsquared : IsShortRoot i.val →
      quotientToIdeal * specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 2) =
        specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) (simplePermutation i) 1) *
          quotientToIdeal) :
    quotientToIdeal * (rootCurve i.val t : Matrix Coordinate Coordinate K) =
      (rootCurve (exceptionalRootPermutation i.val) (exceptionalParameter i.val t) :
        Matrix Coordinate Coordinate K) * quotientToIdeal := by
  rw [← simplePermutation_val, rootCurve_matrix_formula, rootCurve_matrix_formula]
  simp only [rootDividedPower_simple]
  by_cases hi : IsLongRoot i.val
  · rw [exceptionalParameter_of_long hi]
    apply intertwines_cubic_of_linear_coefficients
    · exact hlinear hi
    · exact quotientToIdeal_eDividedPower_two_long i hi
    · simp only [eDividedPower_three, specializeMatrix_zero, mul_zero, zero_mul]
  · rw [exceptionalParameter_of_short hi]
    apply intertwines_cubic_of_squared_coefficients
    · exact quotientToIdeal_eDividedPower_one_short i hi
    · exact hsquared hi
    · simp only [eDividedPower_three, specializeMatrix_zero, mul_zero]
    · apply eDividedPower_two_long_mul_quotientToIdeal
      rw [simplePermutation_val]
      exact (exceptionalRootPermutation_short_iff i.val).mp hi
    · simp only [eDividedPower_three, specializeMatrix_zero, zero_mul]

lemma intertwines_neg_simple_of_coefficients (i : typeF4RootPairing_base.support) (t : K)
    (hlinear : IsLongRoot i.val →
      quotientToIdeal * specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 1) =
        specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) (simplePermutation i) 1) *
          quotientToIdeal)
    (hsquared : IsShortRoot i.val →
      quotientToIdeal * specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 2) =
        specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) (simplePermutation i) 1) *
          quotientToIdeal) :
    letI := typeF4RootPairing.indexNeg
    quotientToIdeal * (rootCurve (-i.val) t : Matrix Coordinate Coordinate K) =
      (rootCurve (exceptionalRootPermutation (-i.val)) (exceptionalParameter (-i.val) t) :
        Matrix Coordinate Coordinate K) * quotientToIdeal := by
  let := typeF4RootPairing.indexNeg
  rw [exceptionalRootPermutation_neg, ← simplePermutation_val, exceptionalParameter_neg,
    rootCurve_matrix_formula, rootCurve_matrix_formula]
  simp only [rootDividedPower_neg_simple]
  by_cases hi : IsLongRoot i.val
  · rw [exceptionalParameter_of_long hi]
    apply intertwines_cubic_of_linear_coefficients
    · exact negative_coefficients_of_positive i (simplePermutation i) 1 1 (hlinear hi)
    · exact negative_coefficients_of_positive i (simplePermutation i) 2 2
        (quotientToIdeal_eDividedPower_two_long i hi)
    · simp only [fDividedPower_three, specializeMatrix_zero, mul_zero, zero_mul]
  · rw [exceptionalParameter_of_short hi]
    apply intertwines_cubic_of_squared_coefficients
    · exact negative_left_zero_of_positive i 1 (quotientToIdeal_eDividedPower_one_short i hi)
    · exact negative_coefficients_of_positive i (simplePermutation i) 2 1 (hsquared hi)
    · simp only [fDividedPower_three, specializeMatrix_zero, mul_zero]
    · apply negative_right_zero_of_positive
      apply eDividedPower_two_long_mul_quotientToIdeal
      rw [simplePermutation_val]
      exact (exceptionalRootPermutation_short_iff i.val).mp hi
    · simp only [fDividedPower_three, specializeMatrix_zero, zero_mul]

/-- Both signs of each numbered simple root from the two positive coefficient comparisons. -/
lemma intertwines_numbered_simple_pair_of_coefficients (m : ℕ) (i : Fin 4)
    (t : CoefficientField m)
    (hlinear : IsLongRoot (typeF4SimpleRootIndex i) →
      quotientToIdeal * specializeMatrix (S := CoefficientField m)
        (eDividedPower (P := typeF4RootPairing) (typeF4RootPairing_baseEquiv i) 1) =
      specializeMatrix (S := CoefficientField m)
        (eDividedPower (P := typeF4RootPairing)
          (simplePermutation (typeF4RootPairing_baseEquiv i)) 1) * quotientToIdeal)
    (hsquared : IsShortRoot (typeF4SimpleRootIndex i) →
      quotientToIdeal * specializeMatrix (S := CoefficientField m)
        (eDividedPower (P := typeF4RootPairing) (typeF4RootPairing_baseEquiv i) 2) =
      specializeMatrix (S := CoefficientField m)
        (eDividedPower (P := typeF4RootPairing)
          (simplePermutation (typeF4RootPairing_baseEquiv i)) 1) * quotientToIdeal) :
    letI := typeF4RootPairing.indexNeg
    (quotientToIdeal * (rootCurve (typeF4SimpleRootIndex i) t :
        Matrix Coordinate Coordinate (CoefficientField m)) =
      (rootCurve (exceptionalRootPermutation (typeF4SimpleRootIndex i))
        (exceptionalParameter (typeF4SimpleRootIndex i) t) :
        Matrix Coordinate Coordinate (CoefficientField m)) * quotientToIdeal) ∧
    (quotientToIdeal * (rootCurve (-typeF4SimpleRootIndex i) t :
        Matrix Coordinate Coordinate (CoefficientField m)) =
      (rootCurve (exceptionalRootPermutation (-typeF4SimpleRootIndex i))
        (exceptionalParameter (-typeF4SimpleRootIndex i) t) :
        Matrix Coordinate Coordinate (CoefficientField m)) * quotientToIdeal) := by
  let := typeF4RootPairing.indexNeg
  exact ⟨intertwines_simple_of_coefficients (typeF4RootPairing_baseEquiv i) t hlinear hsquared,
    intertwines_neg_simple_of_coefficients (typeF4RootPairing_baseEquiv i) t hlinear hsquared⟩

/-- The quotient-to-ideal map intertwines every positive simple-root curve with
its exceptional image in characteristic two. -/
theorem intertwines_simple (i : typeF4RootPairing_base.support) (t : K) :
    quotientToIdeal * (rootCurve i.val t : Matrix Coordinate Coordinate K) =
      (rootCurve (exceptionalRootPermutation i.val) (exceptionalParameter i.val t) :
        Matrix Coordinate Coordinate K) * quotientToIdeal :=
  intertwines_simple_of_coefficients i t
    (quotientToIdeal_eDividedPower_one_long i)
    (quotientToIdeal_eDividedPower_two_short i)

/-- The quotient-to-ideal map intertwines every negative simple-root curve with
its exceptional image in characteristic two. -/
theorem intertwines_neg_simple (i : typeF4RootPairing_base.support) (t : K) :
    letI := typeF4RootPairing.indexNeg
    quotientToIdeal * (rootCurve (-i.val) t : Matrix Coordinate Coordinate K) =
      (rootCurve (exceptionalRootPermutation (-i.val)) (exceptionalParameter (-i.val) t) :
        Matrix Coordinate Coordinate K) * quotientToIdeal :=
  intertwines_neg_simple_of_coefficients i t
    (quotientToIdeal_eDividedPower_one_long i)
    (quotientToIdeal_eDividedPower_two_short i)

/-- The concrete intertwining identity for both signs of all four numbered
simple roots over every Ree coefficient field, including the field of order two. -/
theorem intertwines_numbered_simple_pair (m : ℕ) (i : Fin 4) (t : CoefficientField m) :
    letI := typeF4RootPairing.indexNeg
    (quotientToIdeal * (rootCurve (typeF4SimpleRootIndex i) t :
        Matrix Coordinate Coordinate (CoefficientField m)) =
      (rootCurve (exceptionalRootPermutation (typeF4SimpleRootIndex i))
        (exceptionalParameter (typeF4SimpleRootIndex i) t) :
        Matrix Coordinate Coordinate (CoefficientField m)) * quotientToIdeal) ∧
    (quotientToIdeal * (rootCurve (-typeF4SimpleRootIndex i) t :
        Matrix Coordinate Coordinate (CoefficientField m)) =
      (rootCurve (exceptionalRootPermutation (-typeF4SimpleRootIndex i))
        (exceptionalParameter (-typeF4SimpleRootIndex i) t) :
        Matrix Coordinate Coordinate (CoefficientField m)) * quotientToIdeal) := by
  let := typeF4RootPairing.indexNeg
  exact ⟨intertwines_simple (typeF4RootPairing_baseEquiv i) t,
    intertwines_neg_simple (typeF4RootPairing_baseEquiv i) t⟩

end ReeF4.WordRelations
