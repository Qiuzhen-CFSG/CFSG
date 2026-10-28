module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ThreeSixthWideData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Identity

/-!
# Closing-square rows 224 through 447

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
private theorem product07 : threeSixthTagged07.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows07 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product08 : threeSixthTagged08.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows08 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product09 : threeSixthTagged09.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows09 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product10 : threeSixthTagged10.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows10 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product11 : threeSixthTagged11.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows11 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product12 : threeSixthTagged12.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows12 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product13 : threeSixthTagged13.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows13 := by decide +kernel

/-- Complete row-product comparisons for this consecutive 224-row interval. -/
theorem batch01 : [threeSixthTagged07.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged08.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged09.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged10.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged11.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged12.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged13.map (rowFast 1792 32 threeSixthRows threeSixthWide)] =
    [identityRows07, identityRows08, identityRows09, identityRows10, identityRows11, identityRows12, identityRows13] := by
  rw [product07, product08, product09, product10, product11, product12, product13]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ClosingRows
