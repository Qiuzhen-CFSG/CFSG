module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.Quartic
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.RankOne
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.QuadraticComparison

/-!
# Assembly of the higher positive-simple root coefficients

Degree four is proved for every root by the root-column geometry in
`RootHigher.Quartic`. For degree two, `RootHigher.RankOne` proves signed
integral comparisons at the positive and negative simple roots, and
`RootHigher.QuadraticComparison` proves equality after specialization for
every other root. Together with the degree-one identity, these comparisons
give all degree-two coefficients of the actual routed adjoint operators.

The final theorem retains only the degree-one hypothesis; the integral and
specialized comparison interfaces are also preserved. The matrices and
divided powers are those of Geck's construction in `IntegralGeckConstruction`
and `IntegralAllRootOperators`, with root geometry from `F4RootPairing`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple

/-- The quartic and rank-one cases are discharged. Only the other signed
integral quadratic comparisons remain as additional premises. -/
theorem positive_root_coefficients_two_four_of_integral_sign
    (m : ℕ) (i : typeF4RootPairing_base.support)
    (h1 : ∀ r : typeF4Roots, CoefficientIdentity m i (Sum.inr r) 1)
    (hIntegral : ∀ r : typeF4Roots, r ≠ (i : typeF4Roots) →
      (letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots)) →
      ∃ ε : ℤ, ε ^ 2 = 1 ∧ integralQuadraticOperator i r = ε • integralQuadraticColumn i r) :
    (∀ r : typeF4Roots, CoefficientIdentity m i (Sum.inr r) 2) ∧
      (∀ r : typeF4Roots, CoefficientIdentity m i (Sum.inr r) 4) := by
  classical
  let := typeF4RootPairing.indexNeg
  refine ⟨?_, positive_root_coefficient_four m i⟩
  intro r
  apply coefficientIdentity_two_of_integral_sign m i r (h1 r)
  by_cases hpos : r = (i : typeF4Roots)
  · subst r
    exact integralQuadraticComparison_simple i
  by_cases hneg : r = -(i : typeF4Roots)
  · subst r
    exact integralQuadraticComparison_negative_simple i
  exact hIntegral r hpos hneg

/-- Specialized quadratic comparisons outside the two simple rank-one cases
suffice for degrees two and four. The rank-one cases are already proved. -/
theorem positive_root_coefficients_two_four_of_integral_map_eq
    (m : ℕ) (i : typeF4RootPairing_base.support)
    (h1 : ∀ r : typeF4Roots, CoefficientIdentity m i (Sum.inr r) 1)
    (hIntegral : ∀ r : typeF4Roots, r ≠ (i : typeF4Roots) →
      (letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots)) →
      (integralQuadraticOperator i r).map (Int.castRingHom (CoefficientField m)) =
        (integralQuadraticColumn i r).map (Int.castRingHom (CoefficientField m))) :
    (∀ r : typeF4Roots, CoefficientIdentity m i (Sum.inr r) 2) ∧
      (∀ r : typeF4Roots, CoefficientIdentity m i (Sum.inr r) 4) := by
  classical
  let := typeF4RootPairing.indexNeg
  refine ⟨?_, positive_root_coefficient_four m i⟩
  intro r
  by_cases hpos : r = (i : typeF4Roots)
  · subst r
    exact coefficientIdentity_two_of_integral_sign m i i (h1 i)
      (integralQuadraticComparison_simple i)
  by_cases hneg : r = -(i : typeF4Roots)
  · subst r
    exact coefficientIdentity_two_of_integral_sign m i (-i) (h1 (-i))
      (integralQuadraticComparison_negative_simple i)
  exact coefficientIdentity_two_of_integral_map_eq m i r (h1 r) (hIntegral r hpos hneg)

/-- For the actual routed operators, degree one implies all quadratic and
quartic root coefficients, with no further comparison hypothesis. -/
theorem positive_root_coefficients_two_four
    (m : ℕ) (i : typeF4RootPairing_base.support)
    (h1 : ∀ r : typeF4Roots, CoefficientIdentity m i (Sum.inr r) 1) :
    (∀ r : typeF4Roots, CoefficientIdentity m i (Sum.inr r) 2) ∧
      (∀ r : typeF4Roots, CoefficientIdentity m i (Sum.inr r) 4) := by
  exact positive_root_coefficients_two_four_of_integral_map_eq m i h1
    (integralQuadraticComparison_other_map m i)

end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
