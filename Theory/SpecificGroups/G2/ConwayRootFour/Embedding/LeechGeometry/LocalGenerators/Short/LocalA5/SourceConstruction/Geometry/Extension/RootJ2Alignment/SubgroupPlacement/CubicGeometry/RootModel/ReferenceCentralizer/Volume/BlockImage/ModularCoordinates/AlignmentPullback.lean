module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteModel

/-!
# Pulling reference scalars back through an integral alignment

The scalar-image equality in an alignment pulls the literal order-three
element `y` and every element of `U` back to rational icosian scalars.
Conjugation and the injective five-point scalar map preserve their projective
orders. Thus vectors fixed by all square-one projective rational scalars
transport into the literal `U`-fixed space, with the correct `y` action.

For the cubic action, conjugate the exact reference lift back by the same
integral isometry. The alignment's rational intertwining equation and the
explicit `CubicIntegral` identity let `binaryEquiv_action` descend this
action through the integral lattice basis and its quotient modulo two.

This proves the alignment comparison consumed by
`referenceBlockCoordinates_of_finiteData`. The integral cubic identity and
the alignment remain explicit inputs; this does not assert their existence.

Source consumer: Aschbacher, *Sporadic Groups* (1994), 49.5, pp.283–284.
The imported John Bray ATLAS matrices and Gerald Höhn Leech comparison
(revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917) retain the ATLAS
Research and Attribution License 1.0. See LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section

open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates
open Long.Block Long.Block.Realization

private theorem scalar_pullback (d : Alignment) {a : LeechCentralQuotient}
    (ha : a ∈ I) :
    ∃ u : rationalScalarUnits,
      (MulAut.conj (leechCentralProjection d.conjugator))
        (scalarFive (rationalScalarToFive u)) = a := by
  rw [← d.scalars] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  obtain ⟨s, hs, rfl⟩ := hb
  obtain ⟨u, rfl⟩ := hs
  exact ⟨u, rfl⟩

private theorem scalar_conj_action (d : Alignment) (u : rationalScalarUnits) (v : Binary) :
    quotientModTwoRepresentation
        ((MulAut.conj (leechCentralProjection d.conjugator))
          (scalarFive (rationalScalarToFive u))) (transportedBinary d v) =
      transportedBinary d (scalarAction u v) := by
  rw [MulAut.conj_apply, rationalScalarToFive_projection, map_mul, map_mul, map_inv,
    quotientModTwoRepresentation_compatible, quotientModTwoRepresentation_compatible]
  change leechModTwoRepresentation d.conjugator
    (leechModTwoRepresentation (icosianScalarsToCo0 u.val)
      ((leechModTwoRepresentation d.conjugator).symm
        (leechModTwoRepresentation d.conjugator (binaryEquiv v)))) =
    leechModTwoRepresentation d.conjugator
      (binaryEquiv (binaryEquiv.symm
        (leechModTwoRepresentation (icosianScalarsToCo0 u.val) (binaryEquiv v))))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

private theorem fixed_transport (d : Alignment) (v : Binary) (hv : ScalarFixed v) :
    transportedBinary d v ∈ fixedSpace := by
  intro a ha
  obtain ⟨u, hu⟩ := scalar_pullback d (U_le_I ha)
  have ha2 : a ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨a, ha⟩ : U))
  have hu2 : rationalScalarToFive u ^ 2 = 1 := by
    apply scalarFive_injective
    apply (MulAut.conj (leechCentralProjection d.conjugator)).injective
    rw [map_pow, map_pow, hu, ha2, map_one, map_one]
  rw [← hu, scalar_conj_action, hv u hu2]

private theorem cubic_transport (d : Alignment) (hc : CubicIntegral d.inverse)
    (v : Binary) :
    quotientModTwoRepresentation referenceCubic (transportedBinary d v) =
      transportedBinary d (cubicAction d.inverse v) := by
  let g : LeechIsometryGroup :=
    d.conjugator⁻¹ * icosianHermitianToCo0 referenceLift * d.conjugator
  have hg (x : Space) : (fullIsometryEquiv g).val (matrixComparison x) =
      matrixComparison (cubicMatrix d.inverse *ᵥ x) := by
    change (fullIsometryEquiv
      (d.conjugator⁻¹ * icosianHermitianToCo0 referenceLift * d.conjugator)).val _ = _
    rw [map_mul, map_mul, map_inv]
    change (fullIsometryEquiv d.conjugator).val.symm
      ((fullIsometryEquiv (icosianHermitianToCo0 referenceLift)).val
        ((fullIsometryEquiv d.conjugator).val (matrixComparison x))) = _
    rw [d.cubic, LinearEquiv.symm_apply_apply]
  have he := binaryEquiv_action g (cubicMatrix d.inverse)
    (cubicCoordinates d.inverse) hc hg v
  change leechModTwoRepresentation
    (d.conjugator⁻¹ * icosianHermitianToCo0 referenceLift * d.conjugator)
    (binaryEquiv v) = _ at he
  rw [map_mul, map_mul, map_inv] at he
  have hh := congrArg (leechModTwoRepresentation d.conjugator) he
  change leechModTwoRepresentation d.conjugator
    ((leechModTwoRepresentation d.conjugator).symm
      (leechModTwoRepresentation (icosianHermitianToCo0 referenceLift)
        (leechModTwoRepresentation d.conjugator (binaryEquiv v)))) = _ at hh
  rw [LinearEquiv.apply_symm_apply] at hh
  change quotientModTwoRepresentation
    (leechCentralProjection (icosianHermitianToCo0 referenceLift))
      (leechModTwoRepresentation d.conjugator (binaryEquiv v)) = _
  rw [quotientModTwoRepresentation_compatible]
  exact hh

/-- Pull the literal reference scalar and both quotient actions through the
alignment, using the actual integral cubic coordinate identity. -/
theorem alignmentTransport_exists (d : ReferenceBlock.Alignment)
    (hc : CubicIntegral d.inverse) :
    ∃ u : rationalScalarUnits, orderOf (rationalScalarToFive u) = 3 ∧
      AlignmentTransport d u := by
  obtain ⟨u, hu⟩ := scalar_pullback d (show y ∈ I from ⟨threeCycle, rfl⟩)
  have ho : orderOf (rationalScalarToFive u) = 3 := by
    rw [← orderOf_injective scalarFive scalarFive_injective,
      ← (MulAut.conj (leechCentralProjection d.conjugator)).orderOf_eq, hu, y_order]
  refine ⟨u, ho, ⟨fixed_transport d, ?_, cubic_transport d hc⟩⟩
  intro v
  rw [← hu]
  exact scalar_conj_action d u v

end ReferenceBlock.ModularCoordinates
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
