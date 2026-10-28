module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization

/-!
# Integral transport of the Eisenstein block to the reference pair

An alignment is an actual integral Leech isometry which carries the rational
icosian scalar A₄ to the literal I and intertwines left Eisenstein multiplication
(or its inverse) with the exact commutator-fourth-power reference lift. These
are geometric equations, not assumptions about the desired matrix image.

The block commutes with the rational right scalars and with left Eisenstein
scalars. Conjugating these two identities proves that its projected image lies
in the literal reference common centralizer. The integral and binary action
formulas retain the inverse-adjoint, central-sign and quotient conventions.

This module does not construct an alignment. Its existence and the modular
coordinate comparison are separate inputs to the image-containment assembly.
The source application is Aschbacher, *Sporadic Groups* (1994), 49.2, p.280,
and 49.5, pp.283–284; no distinguished-cubic or root-A₄ recognition theorem is
inferred from an abstract group isomorphism.

The imported matrix and icosian data are John Bray's ATLAS 6L34G1-Ar6aB0
and Gerald Höhn's ATLAS port, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Their ATLAS Research and Attribution License 1.0 is retained in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Atlas.Conway Atlas.Algebra Atlas.Lattices Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock
open Long.Block
open Long.Block.Realization

/-- The actual projective image of the 24 rational norm-one icosians. -/
def scalarImage : Subgroup LeechCentralQuotient :=
  rationalScalarToFive.range.map scalarFive

/-- Left multiplication by the Eisenstein cube root, or its inverse, on all six quaternion coordinates. -/
def cubicMatrix (inverse : Bool) : RealMatrix :=
  realification (Matrix.scalar (Fin 6) (if inverse then eisensteinOmega ^ 2 else eisensteinOmega))

/-- A simultaneous integral comparison with the literal tetrahedral subgroup and reference cubic. -/
structure Alignment where
  conjugator : LeechIsometryGroup
  inverse : Bool
  scalars : scalarImage.map
    (MulAut.conj (leechCentralProjection conjugator)).toMonoidHom = I
  cubic : ∀ x : Space,
    (fullIsometryEquiv (icosianHermitianToCo0 referenceLift)).val
        ((fullIsometryEquiv conjugator).val (matrixComparison x)) =
      (fullIsometryEquiv conjugator).val
        (matrixComparison (cubicMatrix inverse *ᵥ x))

/-- Conjugate the existing integral realization by the supplied actual Leech isometry. -/
def integralHom (d : Alignment) : matrixGroup →* LeechIsometryGroup :=
  (MulAut.conj d.conjugator).toMonoidHom.comp matrixToLeech

/-- Projection uses exactly the existing quotient by the two central signs. -/
def projectiveHom (d : Alignment) : matrixGroup →* LeechCentralQuotient :=
  leechCentralProjection.comp (integralHom d)

/-- The transported rational action retains the inverse-adjoint convention. -/
theorem integralHom_apply (d : Alignment) (g : matrixGroup) (x : Space) :
    (fullIsometryEquiv (integralHom d g)).val
      ((fullIsometryEquiv d.conjugator).val (matrixComparison x)) =
    (fullIsometryEquiv d.conjugator).val
      (matrixComparison (realification g.val.inv.conjTranspose *ᵥ x)) := by
  change (fullIsometryEquiv
    (d.conjugator * matrixToLeech g * d.conjugator⁻¹)).val _ = _
  rw [map_mul, map_mul, map_inv]
  change (fullIsometryEquiv d.conjugator).val
    ((fullIsometryEquiv (matrixToLeech g)).val
      ((fullIsometryEquiv d.conjugator).val.symm
        ((fullIsometryEquiv d.conjugator).val (matrixComparison x)))) = _
  rw [LinearEquiv.symm_apply_apply, matrixToLeech_intertwines]

/-- Scalar-image conjugacy makes the block centralize the literal I. -/
theorem projectiveHom_mem_centralizerI (d : Alignment) (g : matrixGroup) :
    projectiveHom d g ∈ centralizerI := by
  intro a ha
  rw [← d.scalars] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  obtain ⟨s, hs, rfl⟩ := hb
  obtain ⟨u, rfl⟩ := hs
  have hc := (matrixToLeech_scalar g u).symm.map leechCentralProjection
  rw [← rationalScalarToFive_projection] at hc
  have hh := hc.map (MulAut.conj (leechCentralProjection d.conjugator)).toMonoidHom
  change Commute
    (leechCentralProjection d.conjugator * scalarFive (rationalScalarToFive u) *
      (leechCentralProjection d.conjugator)⁻¹)
    (leechCentralProjection d.conjugator * leechCentralProjection (matrixToLeech g) *
      (leechCentralProjection d.conjugator)⁻¹) at hh
  change (leechCentralProjection d.conjugator * scalarFive (rationalScalarToFive u) *
      (leechCentralProjection d.conjugator)⁻¹) *
    leechCentralProjection (d.conjugator * matrixToLeech g * d.conjugator⁻¹) =
    leechCentralProjection (d.conjugator * matrixToLeech g * d.conjugator⁻¹) *
    (leechCentralProjection d.conjugator * scalarFive (rationalScalarToFive u) *
      (leechCentralProjection d.conjugator)⁻¹)
  simpa only [map_mul, map_inv] using hh.eq

/-- The cubic intertwining equation gives integral commutation with the exact reference lift. -/
theorem integralHom_commute_reference (d : Alignment) (g : matrixGroup) :
    Commute (icosianHermitianToCo0 referenceLift) (integralHom d g) := by
  apply fullIsometryEquiv.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ :=
    (matrixComparison.trans (fullIsometryEquiv d.conjugator).val).surjective v
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.trans_apply]
  rw [integralHom_apply, d.cubic, d.cubic, integralHom_apply]
  congr 2
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h := (Matrix.scalar_commute
    (if d.inverse then eisensteinOmega ^ 2 else eisensteinOmega)
    (Commute.all _) g.val.inv.conjTranspose).map realification
  exact congrArg (fun M : RealMatrix => M *ᵥ x) h.eq

/-- Both required commutation relations hold in the actual common centralizer. -/
theorem projectiveHom_mem (d : Alignment) (g : matrixGroup) :
    projectiveHom d g ∈ referenceCentralizer := by
  refine ⟨projectiveHom_mem_centralizerI d g, ?_⟩
  have hc := (integralHom_commute_reference d g).map leechCentralProjection
  change Commute referenceCubic (projectiveHom d g) at hc
  intro a ha
  obtain ⟨n, rfl⟩ := ha
  exact (hc.zpow_left n).eq

/-- The integral comparison produces a homomorphism into the full reference common centralizer. -/
def toReference (d : Alignment) : matrixGroup →* referenceCentralizer :=
  (projectiveHom d).codRestrict referenceCentralizer (projectiveHom_mem d)

/-- The subgroup homomorphism has the prescribed integral lift and projection. -/
theorem toReference_apply (d : Alignment) (g : matrixGroup) :
    (toReference d g).val = leechCentralProjection
      (d.conjugator * matrixToLeech g * d.conjugator⁻¹) := rfl


/-- On an actual eigenspace vector, the transported action is reduction of the
same conjugated integral Leech isometry. -/
theorem toReference_binary (d : Alignment) (g : matrixGroup) (v : ReferenceNatural) :
    (referenceEigenAction referenceScalar (toReference d g) v).val.val =
      leechModTwoRepresentation (integralHom d g) v.val.val := by
  rw [referenceEigenAction_apply]
  exact DFunLike.congr_fun
    (quotientModTwoRepresentation_compatible (integralHom d g)) v.val.val

end ReferenceBlock
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
