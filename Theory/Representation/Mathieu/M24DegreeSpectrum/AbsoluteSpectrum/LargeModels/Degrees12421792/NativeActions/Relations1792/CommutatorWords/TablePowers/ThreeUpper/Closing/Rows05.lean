module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ThreeSixthWideData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Identity

/-!
# Closing-square rows 1120 through 1343

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
private theorem product35 : threeSixthTagged35.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows35 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product36 : threeSixthTagged36.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows36 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product37 : threeSixthTagged37.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows37 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product38 : threeSixthTagged38.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows38 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product39 : threeSixthTagged39.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows39 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product40 : threeSixthTagged40.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows40 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product41 : threeSixthTagged41.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows41 := by decide +kernel

/-- Complete row-product comparisons for this consecutive 224-row interval. -/
theorem batch05 : [threeSixthTagged35.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged36.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged37.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged38.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged39.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged40.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged41.map (rowFast 1792 32 threeSixthRows threeSixthWide)] =
    [identityRows35, identityRows36, identityRows37, identityRows38, identityRows39, identityRows40, identityRows41] := by
  rw [product35, product36, product37, product38, product39, product40, product41]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ClosingRows
