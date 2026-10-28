module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.IntegralReduction
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.QuadraticComparison.Reduction
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.QuadraticComparison.Routes
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.QuadraticComparison.Cartan
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.QuadraticComparison.NoRoot

/-!
# The quadratic root-operator comparison in characteristic two

The actual integral quadratic operator and the linear extension of its second
root column agree after mapping to every Ree coefficient field. Over
characteristic zero, the double-commutator identity gives Lie-algebra
membership and weight `r + 2i`. An absent endpoint forces integral vanishing.
An existing endpoint gives an integral multiple of its Tits-conjugate root
operator; actual-route comparison and Cartan-column detection determine the
coefficient after specialization.

The signed integral reduction and route comparisons remain available. The
coefficient-field theorem below needs no signed integral bracket hypothesis.
Sources: Geck's integral root operators and divided powers, as formalized in
`IntegralGeckConstruction`, `IntegralAllRootOperators`, and
`IntegralChevalleyBrackets`.
-/

public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section

/-- The quadratic operator and the second root-column operator agree over
every coefficient field, for roots other than the two simple rank-one cases. -/
lemma integralQuadraticComparison_other_map (m : ℕ)
    (i : typeF4RootPairing_base.support) (r : typeF4Roots)
    (hpos : r ≠ (i : typeF4Roots))
    (hneg : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots)) :
    (integralQuadraticOperator i r).map (Int.castRingHom (CoefficientField m)) =
      (integralQuadraticColumn i r).map (Int.castRingHom (CoefficientField m)) := by
  classical
  by_cases hr : typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ∈
      Set.range typeF4RootPairing.root
  · obtain ⟨k, hk⟩ := hr
    exact integralQuadraticComparison_map_of_mem_root_line m i r k hpos hneg hk
      (integralQuadraticOperator_map_mem_root_line m i r k hk)
  · rw [integralQuadraticComparison_of_no_root i r hr]

end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
