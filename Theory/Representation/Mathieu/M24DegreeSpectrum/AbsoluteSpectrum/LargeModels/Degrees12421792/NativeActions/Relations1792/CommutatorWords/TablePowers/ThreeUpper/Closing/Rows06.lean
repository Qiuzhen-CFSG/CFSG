module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ThreeSixthWideData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Identity

/-!
# Closing-square rows 1344 through 1567

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
private theorem product42 : threeSixthTagged42.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product43 : threeSixthTagged43.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows43 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product44 : threeSixthTagged44.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows44 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product45 : threeSixthTagged45.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows45 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product46 : threeSixthTagged46.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows46 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product47 : threeSixthTagged47.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows47 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product48 : threeSixthTagged48.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows48 := by decide +kernel

/-- Complete row-product comparisons for this consecutive 224-row interval. -/
theorem batch06 : [threeSixthTagged42.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged43.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged44.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged45.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged46.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged47.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged48.map (rowFast 1792 32 threeSixthRows threeSixthWide)] =
    [identityRows42, identityRows43, identityRows44, identityRows45, identityRows46, identityRows47, identityRows48] := by
  rw [product42, product43, product44, product45, product46, product47, product48]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ClosingRows
