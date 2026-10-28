module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteModel

/-!
# Finite interfaces for the integral-basis coordinate calculation

The right quaternion axes and the half-integral Hurwitz scalar are written
in the actual integral basis. On the common axis-fixed space, changing the
sign of an imaginary half-coordinate adds the identity in characteristic two.
Thus two scalar orientations suffice. The separate scalar comparison must
identify these finite operators with the literal inverse-right icosian action.

The finite embedding is formulated over the computable GoldenFour carrier;
field transport and assembly must preserve the chosen scalarFieldEquiv.
These records do not assert existence of either comparison.

Source consumer: Aschbacher, Sporadic Groups (1994), 49.5, pp.283–284.
The derived tables use John Bray's ATLAS 6L34G1-Ar6aB0 matrices and Gerald
Höhn's integral comparison; see LICEAtlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModelES/ATLAS.txt and LICEAtlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModelES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates.FiniteCalculation
open Long.Block Long.Block.Realization

def rightHalfTable : Matrix Index Index ℤ := fun i j =>
  (![
    ![0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-1,-1,-1,0,-1,-1,-1,0,-1,-1,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,1,1,0,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,1,0,0,0,1,1,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,1,1,1,0,1,0,0,1,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,-1,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,1,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0],
    ![-1,-1,-1,0,0,0,0,0,0,0,0,0,-1,-1,-1,0,-1,-1,-1,-1,0,0,0,0],
    ![1,1,1,1,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,0,0,0,0,0],
    ![0,1,1,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,1,1,0,0,0,0],
    ![0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,1,0,1,0,0,0,0],
    ![-1,-1,-1,0,-1,-1,-1,0,0,0,0,0,-1,-1,-1,0,0,0,0,0,-1,-1,-1,-1],
    ![0,1,1,0,1,1,1,1,0,0,0,0,0,1,1,0,0,0,0,0,1,1,1,0],
    ![0,1,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,1,1],
    ![1,1,1,1,0,1,0,0,0,0,0,0,1,1,1,1,0,0,0,0,1,1,0,1]] : Matrix (Fin 24) (Fin 24) ℤ) (indexNumber i) (indexNumber j)

def rightAxis0Table : Matrix Index Index ℤ := fun i j =>
  (![
    ![0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,1,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-1,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,1,1,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-1,0,-1,0,-1,-1,0,0,-1,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,-1,0,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,-1,0,1,0,-1,1,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,-1,0,-1,-1,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,2,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,-1,0,-1,-1,0,0,0,0,0,0,0,0],
    ![-1,-1,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0,-1,-2,0,0,0,0,0,0],
    ![0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,1,0,0,0,0,0,0],
    ![0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,-1,1,1,0,1,0,0,0,0],
    ![-1,0,-1,-1,0,0,0,0,0,0,0,0,-1,0,-1,-1,0,1,-1,0,0,0,0,0],
    ![-1,0,-1,0,-1,-1,0,0,0,0,0,0,-1,0,-1,0,0,0,0,0,-1,-2,0,0],
    ![0,0,0,-1,0,1,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1,1,0,0],
    ![0,0,0,-1,0,1,0,-1,0,0,0,0,0,0,0,-1,0,0,0,0,1,1,0,1],
    ![0,0,0,0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0]] : Matrix (Fin 24) (Fin 24) ℤ) (indexNumber i) (indexNumber j)

def rightAxis1Table : Matrix Index Index ℤ := fun i j =>
  (![
    ![0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-1,-1,-1,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,-1,-1,-1,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,-1,-1,0,-1,0,-1,0,-1,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-1,0,1,0,1,0,1,1,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,1,1,1,0,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,1,2,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,-1,-2,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0],
    ![-1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,-1,0,-2,0,0,0,0,0],
    ![1,0,1,1,0,0,0,0,0,0,0,0,1,0,1,1,0,0,1,-1,0,0,0,0],
    ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,0,0,0,0],
    ![1,1,1,1,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,0,0,0,0,0],
    ![0,-1,-1,0,-1,0,-1,0,0,0,0,0,0,-1,-1,0,0,0,0,0,-1,0,-2,0],
    ![-1,0,1,0,1,0,1,1,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,1,-1],
    ![0,1,1,1,0,0,1,0,0,0,0,0,0,1,1,1,0,0,0,0,1,0,1,0],
    ![1,1,2,1,1,1,1,1,0,0,0,0,1,1,2,1,0,0,0,0,1,1,1,0]] : Matrix (Fin 24) (Fin 24) ℤ) (indexNumber i) (indexNumber j)

def rightAxis2Table : Matrix Index Index ℤ := fun i j =>
  (![
    ![-1,-1,-1,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,-1,-1,-1,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,1,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-1,-1,0,0,0,-1,-1,0,-1,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,2,1,1,1,1,1,1,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,1,-1,0,0,1,1,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,1,0,1,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,-1,-2,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,0,0,0,0,0,0],
    ![0,-1,-1,0,0,0,0,0,0,0,0,0,0,-1,-1,0,-1,0,0,-2,0,0,0,0],
    ![1,1,1,1,0,0,0,0,0,0,0,0,1,1,1,1,1,0,1,1,0,0,0,0],
    ![0,1,1,1,0,0,0,0,0,0,0,0,0,1,1,1,0,-1,0,1,0,0,0,0],
    ![0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0,0],
    ![-1,-1,0,0,0,-1,-1,0,0,0,0,0,-1,-1,0,0,0,0,0,0,-1,0,0,-2],
    ![1,2,1,1,1,1,1,1,0,0,0,0,1,2,1,1,0,0,0,0,1,0,1,1],
    ![0,1,-1,0,0,1,1,1,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,0,1],
    ![1,1,0,1,0,1,0,0,0,0,0,0,1,1,0,1,0,0,0,0,1,0,0,1]] : Matrix (Fin 24) (Fin 24) ℤ) (indexNumber i) (indexNumber j)

/-- The three pure quaternion axes i, j, and k. -/
def rightAxisTable (k : Fin 3) : Matrix Index Index ℤ :=
  ![rightAxis0Table, rightAxis1Table, rightAxis2Table] k

/-- Simultaneous fixedness under the three displayed quaternion axes. -/
def AxisFixed (v : Binary) : Prop :=
  ∀ k : Fin 3, (rightAxisTable k).map (Int.castRingHom Bit) *ᵥ v = v

/-- Right multiplication by (1+i+j+k)/2, or that operator plus identity.
The second choice is the other projective cubic on the axis-fixed space. -/
def orientationAction (opposite : Bool) : Binary →ₗ[Bit] Binary :=
  (rightHalfTable.map (Int.castRingHom Bit)).mulVecLin +
    if opposite then LinearMap.id else 0

/-- The actual scalar-group comparison, independent of the left cubic and
of the choice of a natural-module embedding. -/
structure ScalarComparison : Prop where
  fixed : ∀ v, AxisFixed v → ScalarFixed v
  cubic : ∀ (u : rationalScalarUnits), orderOf (rationalScalarToFive u) = 3 →
    ∃ opposite : Bool, ∀ v, AxisFixed v → scalarAction u v = orientationAction opposite v

/-- The finite calculation over the computable four-element field.
Both generator equations use the literal retained three-dimensional matrices. -/
structure GoldenCoordinates (inverse opposite : Bool) where
  embed : (Fin 3 → GoldenFour) →+ Binary
  injective : Function.Injective embed
  twist : SL(3,GoldenFour) ≃* SL(3,GoldenFour)
  fixed : ∀ v, AxisFixed (embed v)
  scalar : ∀ (a : GoldenFour) v,
    embed (a • v) = a.re • embed v + a.im • orientationAction opposite (embed v)
  cubic : ∀ v, cubicAction inverse (embed v) = orientationAction opposite (embed v)
  generatorA : ∀ v,
    generatorACoordinates.map (Int.castRingHom Bit) *ᵥ embed v =
      embed ((twist threeA).val *ᵥ v)
  generatorB : ∀ v,
    generatorBCoordinates.map (Int.castRingHom Bit) *ᵥ embed v =
      embed ((twist threeB).val *ᵥ v)

end ReferenceBlock.ModularCoordinates.FiniteCalculation
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
