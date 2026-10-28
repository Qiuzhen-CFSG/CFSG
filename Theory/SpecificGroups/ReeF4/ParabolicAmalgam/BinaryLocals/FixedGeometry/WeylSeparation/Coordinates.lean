module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylLifts

/-!
# Coordinates for binary Ree Weyl separation

We use the actual Cartan-plus-root matrix representation of `Model 0`.
Cartan support and a nonzero simple-root entry are the concrete interfaces
for testing whether a Weyl representative can normalize the positive group.
No Sylow or Bruhat assertion enters these definitions.

Source: Geck's integral representation and the standard positive-chamber
argument for the Borel normalizer; Aschbacher–Smith F.1.12(I)(5),
`refs/quasithin.pdf`, printed pp.263–264.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics.Binary.FixedGeometry.WeylSeparation

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix

/-- The given faithful matrix representation, on its original 52 coordinates. -/
def matrix : Model 0 →* Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
    (CoefficientField 0) :=
  (Units.coeHom _).comp ((Subgroup.subtype _).comp (toSplitGroup 0))

/-- A vector in the span of the simple Cartan basis vectors. -/
def CartanSupported (v : F4Chevalley.BasisIndex → CoefficientField 0) : Prop :=
  ∀ r : F4Chevalley.Root, v (Sum.inr r) = 0

/-- No negative-root coordinate occurs in the vector. -/
def PositiveSupported (v : F4Chevalley.BasisIndex → CoefficientField 0) : Prop :=
  ∀ r : F4Chevalley.Root, ¬ typeF4RootPairing_base.IsPos r → v (Sum.inr r) = 0

/-- A concrete fixed positive matrix detects each simple root on a Cartan column. -/
def SimpleCoordinateWitnesses : Prop :=
  ∀ i : Fin 4, ∃ x ∈ unipotent 0, ∃ j : typeF4RootPairing_base.support,
    matrix x (Sum.inr (typeF4SimpleRootIndex i)) (Sum.inl j) ≠ 0

end ReeF4.Parabolics.Binary.FixedGeometry.WeylSeparation
