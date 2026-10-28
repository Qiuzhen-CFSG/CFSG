module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.Reduction
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.Construction
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.RoutedCurves
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4IntegralChevalleyRepresentation

/-!
# Assembly of adjoint equivariance for the F4 root curves

The operator map is the linear extension of the actual routed root operators
and the simple Cartan commutators. Its value on every root coordinate is proved
in `Construction`. The concrete Tits transport in `RoutedCurves` reduces
equivariance for every root to the positive and negative simple curves.

The theorem here records that reduction with both remaining matrix identities
as explicit premises. It does not assert that those premises are proved.
The intended application is the characteristic-two adjoint lattice used in
the Ree construction, with Geck's integral normalization and the Tits-word
convention of `F4IntegralChevalleyRepresentation`.
-/

public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.SimpleGeckGroup

namespace ReeF4.WordRelations.Faithfulness.Adjoint

/-- Concrete all-root assembly, conditional on the two simple-curve identities. -/
theorem adjointMap_rootCurve_equivariant_of_simple (m : ℕ)
    (he : ∀ (i : typeF4RootPairing_base.support) (t : CoefficientField m),
      Equivariant (adjointMap m) (positiveUnit i t))
    (hf : ∀ (i : typeF4RootPairing_base.support) (t : CoefficientField m),
      Equivariant (adjointMap m) (negativeUnit i t))
    (r : typeF4Roots) (t : CoefficientField m) :
    Equivariant (adjointMap m) (F4Chevalley.rootCurve r t) :=
  rootCurve_equivariant_of_simple (adjointMap m) he hf r t

/-- The required witness and all its identities, once the simple identities hold.
Both premises must be discharged before using this as the adjoint realization. -/
theorem exists_adjointMap_of_simple (m : ℕ)
    (he : ∀ (i : typeF4RootPairing_base.support) (t : CoefficientField m),
      Equivariant (adjointMap m) (positiveUnit i t))
    (hf : ∀ (i : typeF4RootPairing_base.support) (t : CoefficientField m),
      Equivariant (adjointMap m) (negativeUnit i t)) :
    ∃ D : (Coordinate → CoefficientField m) → Matrix Coordinate Coordinate (CoefficientField m),
      (∀ s, IsShortRoot s → D (Pi.single (Sum.inr s) 1) =
        (F4Chevalley.integralOperators.rootOperator s).map
          (Int.castRingHom (CoefficientField m))) ∧
      (∀ r t, Equivariant D (F4Chevalley.rootCurve r t)) :=
  ⟨adjointMap m, fun s _ => adjointMap_root_single m s,
    adjointMap_rootCurve_equivariant_of_simple m he hf⟩

end ReeF4.WordRelations.Faithfulness.Adjoint
