module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.IntegralAlignment.Scalars
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.IntegralAlignment.Word

/-!
# An unconditional integral alignment of the reference pair

An explicit eight-factor word in the integral block and icosian generators
intertwines the Eisenstein cubic with the literal fourth power of the ATLAS
commutator. It centralizes the rational scalar subgroup. A lifted icosian scalar
then carries that subgroup to the literal I and commutes with the reference
lift. Their product therefore satisfies both clauses of ReferenceBlock.Alignment.

All factors are actual integral Leech isometries. Their existing constructions
supply form preservation and both lattice containments. The checked word
identity retains the original Eisenstein orientation and the inverse-adjoint
matrix-action convention. Applying Transport gives a homomorphism into the
literal common centralizer, without a saturation, determinant or recognition
hypothesis.

Source application: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280,
and 49.5, pp.283–284. This is a direct integral construction, using neither
statement as an unproved recognition theorem. The numerical data retain
John Bray's ATLAS 6L34G1-Ar6aB0 and Gerald Höhn's icosian attribution, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Atlas.Conway Atlas.Algebra Atlas.Lattices Matrix
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
open Long.Block Long.Block.Realization

/-- Simultaneous integral alignment of the exact scalar subgroup and reference lift. -/
def referenceBlockAlignment : ReferenceBlock.Alignment := by
  let u := Classical.choose IntegralAlignment.exists_scalar_alignment
  have hu := Classical.choose_spec IntegralAlignment.exists_scalar_alignment
  refine ⟨icosianScalarsToCo0 u * IntegralAlignment.cubicWord, false, ?_, ?_⟩
  · have hc : (MulAut.conj (leechCentralProjection
        (icosianScalarsToCo0 u * IntegralAlignment.cubicWord))).toMonoidHom =
        (MulAut.conj (leechCentralProjection (icosianScalarsToCo0 u))).toMonoidHom.comp
          (MulAut.conj (leechCentralProjection IntegralAlignment.cubicWord)).toMonoidHom := by
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    rw [hc, ← Subgroup.map_map, IntegralAlignment.cubicWord_scalars]
    exact hu
  · intro x
    rw [map_mul]
    change (fullIsometryEquiv (icosianHermitianToCo0 referenceLift)).val
      ((fullIsometryEquiv (icosianScalarsToCo0 u)).val
        ((fullIsometryEquiv IntegralAlignment.cubicWord).val (matrixComparison x))) =
      (fullIsometryEquiv (icosianScalarsToCo0 u)).val
        ((fullIsometryEquiv IntegralAlignment.cubicWord).val
          (matrixComparison (ReferenceBlock.cubicMatrix false *ᵥ x)))
    have hc := ((icosianScalars_commute_Hermitian u referenceLift).symm.map
      fullIsometryEquiv.toMonoidHom).eq
    have hp := congrArg (fun f : rationalLatticeIsometries =>
      f.val ((fullIsometryEquiv IntegralAlignment.cubicWord).val (matrixComparison x))) hc
    change (fullIsometryEquiv (icosianHermitianToCo0 referenceLift)).val
      ((fullIsometryEquiv (icosianScalarsToCo0 u)).val
        ((fullIsometryEquiv IntegralAlignment.cubicWord).val (matrixComparison x))) =
      (fullIsometryEquiv (icosianScalarsToCo0 u)).val
        ((fullIsometryEquiv (icosianHermitianToCo0 referenceLift)).val
          ((fullIsometryEquiv IntegralAlignment.cubicWord).val (matrixComparison x))) at hp
    rw [hp, IntegralAlignment.cubicWord_cubic]

/-- The resulting rational comparison, including the integral conjugator. -/
def referenceBlockComparison : Space ≃ₗ[ℚ] RationalCoordinates :=
  matrixComparison.trans (fullIsometryEquiv referenceBlockAlignment.conjugator).val

/-- The comparison preserves the original block form. -/
theorem referenceBlockComparison_form (x y : Space) :
    rationalForm (referenceBlockComparison x) (referenceBlockComparison y) = form x y :=
  ((fullIsometryEquiv referenceBlockAlignment.conjugator).property.1
    (matrixComparison x) (matrixComparison y)).trans (matrixComparison_form x y)

/-- Both containments hold for the actual integral lattices. -/
theorem referenceBlockComparison_lattice (x : Space) :
    x ∈ lattice ↔ referenceBlockComparison x ∈ rationalLeech :=
  (matrixComparison_lattice x).trans
    ((fullIsometryEquiv referenceBlockAlignment.conjugator).property.2 (matrixComparison x))

/-- Application of the unconditional alignment to the literal common centralizer. -/
def referenceBlockHom : matrixGroup →* referenceCentralizer :=
  ReferenceBlock.toReference referenceBlockAlignment

/-- Its value is the prescribed conjugated integral action followed by the actual sign quotient. -/
theorem referenceBlockHom_apply (g : matrixGroup) :
    (referenceBlockHom g).val = leechCentralProjection
      (referenceBlockAlignment.conjugator * matrixToLeech g *
        referenceBlockAlignment.conjugator⁻¹) :=
  ReferenceBlock.toReference_apply referenceBlockAlignment g

/-- The rational action uses precisely the source inverse adjoint. -/
theorem referenceBlockHom_rational (g : matrixGroup) (x : Space) :
    (fullIsometryEquiv (ReferenceBlock.integralHom referenceBlockAlignment g)).val
      (referenceBlockComparison x) =
      referenceBlockComparison (realification g.val.inv.conjTranspose *ᵥ x) :=
  ReferenceBlock.integralHom_apply referenceBlockAlignment g x

/-- The same lift supplies the actual action on the binary reference eigenspace. -/
theorem referenceBlockHom_binary (g : matrixGroup) (v : ReferenceNatural) :
    (referenceEigenAction referenceScalar (referenceBlockHom g) v).val.val =
      leechModTwoRepresentation (ReferenceBlock.integralHom referenceBlockAlignment g) v.val.val :=
  ReferenceBlock.toReference_binary referenceBlockAlignment g v

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
