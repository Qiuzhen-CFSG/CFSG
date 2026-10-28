module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.Construction
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.RoutedCurves
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.Cartan

/-!+# Assembly of positive-simple adjoint equivariance

The Cartan-coordinate identities for the fixed adjoint map are proved in
`PositiveSimple.Cartan`. The positive F4 curve is quadratic, since the integral
cubic divided power vanishes. On each root coordinate, its adjoint identity
therefore reduces to four matrix coefficients. The first is an operator
commutator, and the others involve the second divided power. Degree three
follows algebraically from degrees one and two, leaving degrees one, two,
and four as the independent root-coordinate obligations.

This module proves the assembly with those root-coordinate coefficients as
explicit premises. It does not assert that they have been established. Their
discharge is needed for unconditional `positive_simple_equivariant`.
All matrices are the actual routed operators from Geck's integral construction
in `IntegralAllRootOperators` and `F4IntegralChevalleyRepresentation`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup

namespace ReeF4.WordRelations.Faithfulness.Adjoint

/-- The Cartan cases are discharged; four root-coordinate coefficients remain. -/
theorem positive_simple_equivariant_of_root_coefficients
    (m : ℕ) (i : typeF4RootPairing_base.support) (t : CoefficientField m)
    (hroot : ∀ (r : typeF4Roots) (d : ℕ), 1 ≤ d → d ≤ 4 →
      PositiveSimple.CoefficientIdentity m i (Sum.inr r) d) :
    Equivariant (adjointMap m) (positiveUnit i t) := by
  apply (equivariant_iff_basis (adjointMap m) _).mpr
  intro j
  rcases j with j | r
  · exact PositiveSimple.positive_cartan_basis m i j t
  · exact PositiveSimple.basis_of_quadratic_coefficients m i (Sum.inr r) t (hroot r)

/-- Only the first, second, and fourth root coefficients require independent proofs. -/
theorem positive_simple_equivariant_of_root_one_two_four
    (m : ℕ) (i : typeF4RootPairing_base.support) (t : CoefficientField m)
    (h1 : ∀ r : typeF4Roots, PositiveSimple.CoefficientIdentity m i (Sum.inr r) 1)
    (h2 : ∀ r : typeF4Roots, PositiveSimple.CoefficientIdentity m i (Sum.inr r) 2)
    (h4 : ∀ r : typeF4Roots, PositiveSimple.CoefficientIdentity m i (Sum.inr r) 4) :
    Equivariant (adjointMap m) (positiveUnit i t) := by
  apply positive_simple_equivariant_of_root_coefficients m i t
  intro r d hd1 hd4
  interval_cases d
  · exact h1 r
  · exact h2 r
  · apply PositiveSimple.coefficientIdentity_three_of_one_two m i (Sum.inr r) (h1 r)
    rintro (j | s)
    · exact PositiveSimple.coefficientIdentity_cartan m i j 2 (by omega) (by omega)
    · exact h2 s
  · exact h4 r

end ReeF4.WordRelations.Faithfulness.Adjoint
