module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ThreeSixthWideData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Identity

/-!
# Closing-square rows 896 through 1119

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
private theorem product28 : threeSixthTagged28.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows28 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product29 : threeSixthTagged29.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows29 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product30 : threeSixthTagged30.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows30 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product31 : threeSixthTagged31.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows31 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product32 : threeSixthTagged32.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows32 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product33 : threeSixthTagged33.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows33 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product34 : threeSixthTagged34.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows34 := by decide +kernel

/-- Complete row-product comparisons for this consecutive 224-row interval. -/
theorem batch04 : [threeSixthTagged28.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged29.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged30.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged31.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged32.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged33.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged34.map (rowFast 1792 32 threeSixthRows threeSixthWide)] =
    [identityRows28, identityRows29, identityRows30, identityRows31, identityRows32, identityRows33, identityRows34] := by
  rw [product28, product29, product30, product31, product32, product33, product34]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ClosingRows
