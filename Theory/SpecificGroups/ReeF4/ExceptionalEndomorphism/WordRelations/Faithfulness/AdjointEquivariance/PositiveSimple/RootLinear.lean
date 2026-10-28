module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.Coefficients
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.Basic
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RouteOperators
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.NoRootSums

/-!
# Assembly of the degree-one root coefficient

The opposite simple root is proved in `RootLinear.Basic`. Every other root
has either a root sum with the acting simple root, or a vanishing column.
This module assembles the degree-one coefficient from the corresponding two
operator commutator identities, proved in `RootLinear.RootSums` and
`RootLinear.NoRootSums`. The resulting identity holds for every root, including
both root lengths and the opposite simple root.

All operators and column formulas use Geck's actual integral construction,
as in `IntegralGeckConstruction` and `IntegralAllRootOperators`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple

/-- The opposite-root case is discharged; the two non-opposite commutator
formulas suffice for every root coefficient. -/
theorem positive_root_coefficient_one_of_commutators
    (m : ℕ) (i : typeF4RootPairing_base.support)
    (hsum : ∀ r s : typeF4Roots,
      typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r →
        dividedPower m i 1 * coordinateOperator m (Sum.inr r) -
          coordinateOperator m (Sum.inr r) * dividedPower m i 1 =
            (typeF4RootPairing.chainBotCoeff i r + 1 : CoefficientField m) •
              coordinateOperator m (Sum.inr s))
    (hzero : ∀ r : typeF4Roots,
      (letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots)) →
      typeF4RootPairing.root i + typeF4RootPairing.root r ∉
        Set.range typeF4RootPairing.root →
          dividedPower m i 1 * coordinateOperator m (Sum.inr r) -
            coordinateOperator m (Sum.inr r) * dividedPower m i 1 = 0)
    (r : typeF4Roots) : CoefficientIdentity m i (Sum.inr r) 1 := by
  let := typeF4RootPairing.indexNeg
  by_cases hopp : r = -(i : typeF4Roots)
  · subst r
    exact positive_root_coefficient_one_opposite m i
  rw [coefficientIdentity_one_iff]
  by_cases h : typeF4RootPairing.root i + typeF4RootPairing.root r ∈
      Set.range typeF4RootPairing.root
  · obtain ⟨s, hs⟩ := h
    rw [columnImage_one_root_add m i r s hs]
    exact (hsum r s hs).symm
  · rw [columnImage_one_root_zero m i r hopp h]
    exact (hzero r hopp h).symm

/-- Every root coordinate satisfies the degree-one positive-simple adjoint identity. -/
theorem positive_root_coefficient_one (m : ℕ) (i : typeF4RootPairing_base.support)
    (r : typeF4Roots) : CoefficientIdentity m i (Sum.inr r) 1 :=
  positive_root_coefficient_one_of_commutators m i
    (positive_root_commutator_add m i) (positive_root_commutator_zero m i) r

end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
