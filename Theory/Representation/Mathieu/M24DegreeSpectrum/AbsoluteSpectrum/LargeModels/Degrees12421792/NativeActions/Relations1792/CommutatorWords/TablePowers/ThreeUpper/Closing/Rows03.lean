module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ThreeSixthWideData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Identity

/-!
# Closing-square rows 672 through 895

Seven blocks of 32 rows are checked synchronously and bundled for the complete
closing-square certificate. Separate modules retain completed kernel checks
across interruptions by the shared machine's aggregate memory guard.

Source: ATLAS M24G1-P1; see `../source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ClosingRows
open Arithmetic GeneratorOrders
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data

set_option Elab.async false

set_option maxRecDepth 8192 in
private theorem product21 : threeSixthTagged21.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows21 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product22 : threeSixthTagged22.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows22 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product23 : threeSixthTagged23.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows23 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product24 : threeSixthTagged24.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows24 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product25 : threeSixthTagged25.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows25 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product26 : threeSixthTagged26.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows26 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product27 : threeSixthTagged27.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows27 := by decide +kernel

/-- Complete row-product comparisons for this consecutive 224-row interval. -/
theorem batch03 : [threeSixthTagged21.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged22.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged23.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged24.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged25.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged26.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged27.map (rowFast 1792 32 threeSixthRows threeSixthWide)] =
    [identityRows21, identityRows22, identityRows23, identityRows24, identityRows25, identityRows26, identityRows27] := by
  rw [product21, product22, product23, product24, product25, product26, product27]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ClosingRows
