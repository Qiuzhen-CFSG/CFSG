module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.Coordinates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.AlignmentPullback

/-!
# Assembly of reference coordinates from the actual integral quotient

The finite calculation supplies an injective additive map into the displayed
integral basis modulo two, together with its scalar rule and generator actions.
The independent alignment comparison transports these vectors to the literal
U-fixed reference eigenspace. The scalar rule makes the resulting map F₄-linear;
the proved eigenspace dimension bound makes its injection surjective.

The finite calculation proves integrality for both cubic orientations and
constructs coordinates for every rational scalar of projective order three.
The alignment comparison pulls back the literal scalar y with that order.
Combining them constructs the complete published Coordinates record for every
explicit alignment, including both literal integral generator equations, ready
for BlockImage.coverage_of_coordinates. Only the alignment remains an input.

Source consumer: Aschbacher, *Sporadic Groups* (1994), 49.5, pp.283–284.
The imported John Bray matrices and Gerald Höhn Leech comparison retain the
ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
open ReferenceBlock.ModularCoordinates

/-- Assemble the finite integral-basis calculation and the geometric scalar
comparison into the literal coordinate witness consumed by coverage. -/
theorem referenceBlockCoordinates_of_finiteData (d : ReferenceBlock.Alignment)
    (u : Long.Block.Realization.rationalScalarUnits)
    (h : AlignmentTransport d u) (c : FiniteCoordinates d.inverse u) :
    Nonempty (ReferenceBlock.Coordinates d) := by
  let j : (Fin 3 → F) →ₗ[F] ReferenceNatural :=
    { toFun := fun v =>
        ⟨⟨transportedBinary d (c.embed v), h.fixed _ (c.fixed v)⟩, by
          apply (mem_referenceEigenspace_scalar_iff _).mpr
          change quotientModTwoRepresentation referenceCubic
            (transportedBinary d (c.embed v)) =
            quotientModTwoRepresentation y (transportedBinary d (c.embed v))
          rw [h.cubic, h.scalar, c.cubic]⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        apply Subtype.ext
        change transportedBinary d (c.embed (v + w)) = _
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro a v
        apply Subtype.ext
        apply Subtype.ext
        change transportedBinary d (c.embed (a • v)) =
          (a • (⟨transportedBinary d (c.embed v), h.fixed _ (c.fixed v)⟩ : fixedSpace)).val
        rw [Long.smul_val, c.scalar, map_add, map_smul, map_smul, h.scalar] }
  have hj : Function.Injective j := by
    intro v w he
    apply c.injective
    apply (transportedBinary d).injective
    exact congrArg (fun v : ReferenceNatural => v.val.val) he
  have hdim : Module.finrank F (Fin 3 → F) = Module.finrank F ReferenceNatural := by
    have hl := LinearMap.finrank_le_finrank_of_injective hj
    have hu := referenceEigenspace_finrank_le_three
    simpa using Nat.le_antisymm hl (by simpa using hu)
  let e := LinearEquiv.ofBijective j
    ⟨hj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hj⟩
  refine ⟨⟨e, c.twist, ?_, ?_⟩⟩
  · intro v
    apply Subtype.ext
    apply Subtype.ext
    rw [ReferenceBlock.toReference_binary]
    change leechModTwoRepresentation (ReferenceBlock.integralHom d Long.Block.matrixGeneratorA)
      (transportedBinary d (c.embed v)) = transportedBinary d (c.embed _)
    rw [transportedBinary_generatorA, c.generatorA]
  · intro v
    apply Subtype.ext
    apply Subtype.ext
    rw [ReferenceBlock.toReference_binary]
    change leechModTwoRepresentation (ReferenceBlock.integralHom d Long.Block.matrixGeneratorB)
      (transportedBinary d (c.embed v)) = transportedBinary d (c.embed _)
    rw [transportedBinary_generatorB, c.generatorB]

/-- Every explicit integral alignment supplies the actual F₄-linear reference
coordinates and an SL₃(4) automorphism satisfying both literal generator equations.
This discharges the coordinate premise of `ReferenceBlock.coverage_of_coordinates`;
constructing the alignment remains with the reference-image assembly. -/
theorem referenceBlockCoordinates (d : ReferenceBlock.Alignment) :
    Nonempty (ReferenceBlock.Coordinates d) := by
  obtain ⟨u, hu, h⟩ := alignmentTransport_exists d (cubicCoordinates_integral d.inverse)
  obtain ⟨c⟩ := finiteCoordinates d.inverse u hu
  exact referenceBlockCoordinates_of_finiteData d u h c

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel

