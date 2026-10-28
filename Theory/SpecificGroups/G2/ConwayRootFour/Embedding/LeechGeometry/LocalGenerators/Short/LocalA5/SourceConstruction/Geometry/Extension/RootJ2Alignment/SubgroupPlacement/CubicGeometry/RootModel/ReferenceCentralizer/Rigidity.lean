module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Coordinates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Rigidity.PairedAction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Rigidity.Pairing
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness

/-!
# The reference eigenspace's sign kernel

The paired-eigenspace reduction transfers pointwise fixation on the selected
reference eigenspace to the whole literal U-fixed space. An independent
integral kernel theorem on that whole space then gives exactly the original
two central signs. Applying `referenceEigenAction_injective_of_lift_kernel`
turns this into faithfulness on the quotient.

The constructed invariant pairing and the proved whole-fixed-space faithfulness
discharge both geometric inputs in `referenceEigen_lift_kernel`. This proves
faithfulness of the actual eigenspace action without any extra premise. The
independent determinant proof belongs to the reference-centralizer assembly.

Source: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and 49.5, p.283.
-/

public noncomputable section
open Atlas.Conway Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long

/-- Conditional integral assembly, retaining the independently owned geometric
kernel assertion on all U-fixed vectors. -/
theorem referenceEigen_lift_kernel_of_pairing
    (B : ReferenceInvariantPairing)
    (hfixed : ∀ g : LeechIsometryGroup, leechCentralProjection g ∈ centralizerI →
      (∀ v ∈ fixedSpace, leechModTwoRepresentation g v = v) → g ∈ leechCentralSigns)
    (g : LeechIsometryGroup) (hg : leechCentralProjection g ∈ referenceCentralizer)
    (hfix : ∀ v ∈ fixedSpace,
      quotientModTwoRepresentation referenceCubic v = quotientModTwoRepresentation y v →
        leechModTwoRepresentation g v = v) : g ∈ leechCentralSigns :=
  hfixed g hg.1 (referenceEigen_fixes_fixedSpace_of_pairing B g hg hfix)

/-- Immediate application to the published eigenspace-action consumer. The
pairing and full-fixed-space geometry are not discharged by this application. -/
theorem referenceEigenAction_injective_of_pairing
    (B : ReferenceInvariantPairing)
    (hfixed : ∀ g : LeechIsometryGroup, leechCentralProjection g ∈ centralizerI →
      (∀ v ∈ fixedSpace, leechModTwoRepresentation g v = v) → g ∈ leechCentralSigns) :
    Function.Injective (referenceEigenAction referenceScalar) :=
  referenceEigenAction_injective_of_lift_kernel (referenceEigen_lift_kernel_of_pairing B hfixed)

/-- An integral isometry centralizing the actual reference cubic and tetrahedral
scalars, and fixing the selected eigenspace pointwise, is one of the original
two central signs. Both the pairing and full-fixed-space kernel are discharged. -/
theorem referenceEigen_lift_kernel
    (g : LeechIsometryGroup) (hg : leechCentralProjection g ∈ referenceCentralizer)
    (hfix : ∀ v ∈ fixedSpace,
      quotientModTwoRepresentation referenceCubic v = quotientModTwoRepresentation y v →
        leechModTwoRepresentation g v = v) : g ∈ leechCentralSigns := by
  obtain ⟨B⟩ := nonempty_referenceInvariantPairing
  apply referenceEigen_lift_kernel_of_pairing B ?_ g hg hfix
  intro h hh hfixed
  rw [← leechCentralProjection_kernel]
  apply MonoidHom.mem_ker.mpr
  apply centralizerFaithful _ hh
  simpa only [quotientModTwoRepresentation_compatible] using hfixed

/-- The actual common centralizer acts faithfully on the selected reference
eigenspace after quotienting by exactly the original two central signs. -/
theorem referenceEigenAction_injective :
    Function.Injective (referenceEigenAction referenceScalar) :=
  referenceEigenAction_injective_of_lift_kernel referenceEigen_lift_kernel

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
