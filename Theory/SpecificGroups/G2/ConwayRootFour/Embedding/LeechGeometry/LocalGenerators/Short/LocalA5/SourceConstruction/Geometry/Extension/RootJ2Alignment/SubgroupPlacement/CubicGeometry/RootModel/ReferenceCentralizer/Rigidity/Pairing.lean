module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Rigidity.PairedAction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Rigidity.Pairing.BinaryDescent
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Rigidity.Pairing.ScalarExtension

/-!
# The actual invariant pairing for the reference eigenspaces

Descend the nondegenerate binary Leech polar form through the tetrahedral
involution's difference operator, then recover the four-element-field form
using the actual scalar Y. No long frame, faithfulness, determinant, or
identification of the centralizer is assumed. The resulting pairing gives
the unconditional equality of the selected-eigenspace and full-fixed-space
kernels, the exact consumer from `PairedAction`.

Source context: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and the
natural-plus-dual action in 49.5, p.283. Imported lattice models retain their
ATLAS attribution and inverse-right-scalar convention.
-/

public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long

/-- The literal U-fixed Leech space has an invariant nondegenerate F-bilinear form. -/
theorem nonempty_referenceInvariantPairing : Nonempty ReferenceInvariantPairing :=
  ⟨PairingScalar.ofBinary PairingBinary.form PairingBinary.form_nondegenerate
    PairingBinary.form_balanced PairingBinary.form_invariant⟩

/-- Application to the actual selected-eigenspace action; exclusion of the
remaining full-fixed-space kernel is the separate lattice-faithfulness problem. -/
theorem referenceEigenAction_ker_eq :
    (referenceEigenAction referenceScalar).ker = referenceFixedAction.ker := by
  obtain ⟨B⟩ := nonempty_referenceInvariantPairing
  exact referenceEigenAction_ker_eq_of_pairing B

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
