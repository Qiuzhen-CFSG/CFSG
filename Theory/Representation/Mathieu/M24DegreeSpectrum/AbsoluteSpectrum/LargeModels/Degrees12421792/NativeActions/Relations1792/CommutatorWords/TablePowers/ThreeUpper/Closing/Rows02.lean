module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ThreeSixthWideData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Identity

/-!
# Closing-square rows 448 through 671

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
private theorem product14 : threeSixthTagged14.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows14 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product15 : threeSixthTagged15.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows15 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product16 : threeSixthTagged16.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows16 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product17 : threeSixthTagged17.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows17 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product18 : threeSixthTagged18.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows18 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product19 : threeSixthTagged19.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows19 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product20 : threeSixthTagged20.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows20 := by decide +kernel

/-- Complete row-product comparisons for this consecutive 224-row interval. -/
theorem batch02 : [threeSixthTagged14.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged15.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged16.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged17.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged18.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged19.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged20.map (rowFast 1792 32 threeSixthRows threeSixthWide)] =
    [identityRows14, identityRows15, identityRows16, identityRows17, identityRows18, identityRows19, identityRows20] := by
  rw [product14, product15, product16, product17, product18, product19, product20]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ClosingRows
