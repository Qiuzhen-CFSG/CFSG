module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.LinearExtension
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4IntegralChevalleyRepresentation

/-!
# The candidate adjoint map on the actual F4 lattice

Send each root coordinate to its routed integral root operator, specialized to
the Ree coefficient field. Send a simple Cartan coordinate to the commutator
of the corresponding positive and negative simple operators, and extend
linearly. This fixes the map independently of any equivariance assertion.

The root-coordinate identities follow from finite-basis linear extension.
Equivariance requires further matrix identities; it is not asserted here.
The lattice and normalization are those of Geck's integral construction, as
implemented in `F4IntegralChevalleyRepresentation`.
-/

@[expose] public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction

namespace ReeF4.WordRelations.Faithfulness.Adjoint

/-- The specified operator on every Cartan or root coordinate. -/
noncomputable def coordinateOperator (m : ℕ) :
    Coordinate → Matrix Coordinate Coordinate (CoefficientField m)
  | Sum.inr r => (F4Chevalley.integralOperators.rootOperator r).map
      (Int.castRingHom (CoefficientField m))
  | Sum.inl i =>
      let E := (eMatrix (P := typeF4RootPairing) i).map
        (Int.castRingHom (CoefficientField m))
      let F := (fMatrix (P := typeF4RootPairing) i).map
        (Int.castRingHom (CoefficientField m))
      E * F - F * E

/-- Linear extension of the actual specialized coordinate operators. -/
noncomputable def adjointMap (m : ℕ) :
    (Coordinate → CoefficientField m) →ₗ[CoefficientField m]
      Matrix Coordinate Coordinate (CoefficientField m) :=
  linearExtension (coordinateOperator m)

theorem adjointMap_single (m : ℕ) (j : Coordinate) :
    adjointMap m (Pi.single j 1) = coordinateOperator m j :=
  linearExtension_single (coordinateOperator m) j

/-- In particular, the required value holds on every short root (and every long root). -/
theorem adjointMap_root_single (m : ℕ) (r : typeF4Roots) :
    adjointMap m (Pi.single (Sum.inr r) 1) =
      (F4Chevalley.integralOperators.rootOperator r).map
        (Int.castRingHom (CoefficientField m)) :=
  adjointMap_single m (Sum.inr r)

theorem adjointMap_cartan_single (m : ℕ) (i : typeF4RootPairing_base.support) :
    adjointMap m (Pi.single (Sum.inl i) 1) =
      (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) *
        (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) -
      (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) *
        (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) :=
  adjointMap_single m (Sum.inl i)

end ReeF4.WordRelations.Faithfulness.Adjoint
