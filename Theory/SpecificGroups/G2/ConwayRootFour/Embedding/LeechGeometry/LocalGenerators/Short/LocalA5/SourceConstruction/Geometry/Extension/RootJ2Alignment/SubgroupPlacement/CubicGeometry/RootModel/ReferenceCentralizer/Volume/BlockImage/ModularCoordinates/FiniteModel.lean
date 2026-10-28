module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.IntegralQuotient

/-!
# Finite matrices and scalar orientations for reference coordinates

These interfaces separate two genuine comparisons. The finite problem is
to find a six-dimensional binary column space in the displayed integral
basis, with the correct F₄ scalar action and two generator matrices.
The geometric problem pulls the literal U and Y back through an arbitrary
integral alignment. Neither comparison is assumed to exist here.

The rational candidate for left ω is conjugated by the integral basis
before its integer numerator is taken. The separate `CubicIntegral`
identity must certify that this is the actual integral coordinate matrix;
using the numerator alone is not a reduction of rational coordinates.

Source: Aschbacher, *Sporadic Groups* (1994), 49.5, pp.283–284.
The John Bray matrices and Gerald Höhn integral comparison retain the ATLAS
Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates
open Long.Block Long.Block.Realization

abbrev Binary := Index → Bit

/-- The actual inverse-right scalar action, expressed in the integral basis. -/
def scalarAction (u : rationalScalarUnits) : Binary ≃ₗ[Bit] Binary :=
  (binaryEquiv.trans (leechModTwoRepresentation (icosianScalarsToCo0 u.val))).trans
    binaryEquiv.symm

/-- Fixed by the projective quaternion four-group, including its identity. -/
def ScalarFixed (v : Binary) : Prop :=
  ∀ s : rationalScalarUnits, rationalScalarToFive s ^ 2 = 1 → scalarAction s v = v

/-- Candidate integer coordinates for left ω or ω². Integrality is a separate
checked identity, not a convention for reducing rational numbers. -/
def cubicCoordinates (inverse : Bool) : Matrix Index Index ℤ :=
  fun i j => ((basisInverse.map (Int.castRingHom ℚ) *
    cubicMatrix inverse * basisMatrix) i j).num

/-- Exact compatibility with the actual integral basis. -/
def CubicIntegral (inverse : Bool) : Prop :=
  cubicMatrix inverse * basisMatrix =
    basisMatrix * (cubicCoordinates inverse).map (Int.castRingHom ℚ)

def cubicAction (inverse : Bool) : Binary →ₗ[Bit] Binary :=
  ((cubicCoordinates inverse).map (Int.castRingHom Bit)).mulVecLin

/-- Concrete finite data for a projective cubic scalar and a left-cubic
orientation. The injection, scalar rule and matrix actions must be proved. -/
structure FiniteCoordinates (inverse : Bool) (u : rationalScalarUnits) where
  embed : (Fin 3 → F) →+ Binary
  injective : Function.Injective embed
  twist : SL(3,F) ≃* SL(3,F)
  fixed : ∀ v, ScalarFixed (embed v)
  scalar : ∀ (a : F) v,
    embed (a • v) = (Long.scalarFieldEquiv a).re • embed v +
      (Long.scalarFieldEquiv a).im • scalarAction u (embed v)
  cubic : ∀ v, cubicAction inverse (embed v) = scalarAction u (embed v)
  generatorA : ∀ v,
    generatorACoordinates.map (Int.castRingHom Bit) *ᵥ embed v =
      embed ((twist (matrixQuotient matrixGeneratorA)).val *ᵥ v)
  generatorB : ∀ v,
    generatorBCoordinates.map (Int.castRingHom Bit) *ᵥ embed v =
      embed ((twist (matrixQuotient matrixGeneratorB)).val *ᵥ v)

/-- The geometric comparison needed for the finite calculation. In particular,
the scalar on the right is the pulled-back literal Y, not the ATLAS yLift. -/
structure AlignmentTransport (d : Alignment) (u : rationalScalarUnits) : Prop where
  fixed : ∀ v, ScalarFixed v → transportedBinary d v ∈ fixedSpace
  scalar : ∀ v, quotientModTwoRepresentation y (transportedBinary d v) =
    transportedBinary d (scalarAction u v)
  cubic : ∀ v, quotientModTwoRepresentation referenceCubic (transportedBinary d v) =
    transportedBinary d (cubicAction d.inverse v)

end ReferenceBlock.ModularCoordinates
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel

