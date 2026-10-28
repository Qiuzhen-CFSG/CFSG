module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ThreeSixthWideData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Identity

/-!
# Closing-square rows 1568 through 1791

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
private theorem product49 : threeSixthTagged49.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows49 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product50 : threeSixthTagged50.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows50 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product51 : threeSixthTagged51.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows51 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product52 : threeSixthTagged52.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows52 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product53 : threeSixthTagged53.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows53 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product54 : threeSixthTagged54.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows54 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product55 : threeSixthTagged55.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows55 := by decide +kernel

/-- Complete row-product comparisons for this consecutive 224-row interval. -/
theorem batch07 : [threeSixthTagged49.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged50.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged51.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged52.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged53.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged54.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged55.map (rowFast 1792 32 threeSixthRows threeSixthWide)] =
    [identityRows49, identityRows50, identityRows51, identityRows52, identityRows53, identityRows54, identityRows55] := by
  rw [product49, product50, product51, product52, product53, product54, product55]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ClosingRows
