module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.Basic
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RouteOperators
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums.Columns
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums.RootSpace

/-!+# Positive-simple commutators when the root sum exists

The commutator of the actual routed operators lies in the sum-root operator
line by characteristic-zero Lie root-space multiplicity one and integral
primitivity. Its action on Cartan columns determines the scalar after
specialization to characteristic two. This proves the operator identity with
Geck's lower-root-string coefficient, for both short and long input roots.

Sources: Geck's integral construction and root-string formulas, implemented in
`IntegralGeckConstruction`, `IntegralAllRootOperators`, and
`IntegralChevalleyBrackets`; the root-space argument is in `RootSums.RootSpace`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple

/-- The positive-simple operator commutator when the root sum exists. -/
theorem positive_root_commutator_add (m : ℕ) (i : typeF4RootPairing_base.support)
    (r s : typeF4Roots)
    (h : typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r) :
    dividedPower m i 1 * coordinateOperator m (Sum.inr r) -
      coordinateOperator m (Sum.inr r) * dividedPower m i 1 =
        (typeF4RootPairing.chainBotCoeff i r + 1 : CoefficientField m) •
          coordinateOperator m (Sum.inr s) :=
  positive_root_commutator_add_of_mem_line m i r s h
    (RootSumSpace.positive_root_commutator_mem_line m i r s h)

/-- Every root-sum column satisfies the degree-one coefficient identity. -/
theorem positive_root_coefficient_one_add (m : ℕ) (i : typeF4RootPairing_base.support)
    (r s : typeF4Roots)
    (h : typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r) :
    CoefficientIdentity m i (Sum.inr r) 1 := by
  rw [coefficientIdentity_one_iff, columnImage_one_root_add m i r s h]
  exact (positive_root_commutator_add m i r s h).symm

end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
