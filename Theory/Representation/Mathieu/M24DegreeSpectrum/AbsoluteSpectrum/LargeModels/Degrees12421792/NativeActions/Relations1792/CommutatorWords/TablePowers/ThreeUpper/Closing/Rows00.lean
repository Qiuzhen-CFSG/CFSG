module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ThreeSixthWideData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Identity

/-!
# Closing-square rows 0 through 223

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
private theorem product00 : threeSixthTagged00.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows00 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product01 : threeSixthTagged01.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows01 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product02 : threeSixthTagged02.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows02 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product03 : threeSixthTagged03.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows03 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product04 : threeSixthTagged04.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows04 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product05 : threeSixthTagged05.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows05 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product06 : threeSixthTagged06.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows06 := by decide +kernel

/-- Complete row-product comparisons for this consecutive 224-row interval. -/
theorem batch00 : [threeSixthTagged00.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged01.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged02.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged03.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged04.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged05.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged06.map (rowFast 1792 32 threeSixthRows threeSixthWide)] =
    [identityRows00, identityRows01, identityRows02, identityRows03, identityRows04, identityRows05, identityRows06] := by
  rw [product00, product01, product02, product03, product04, product05, product06]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ClosingRows
