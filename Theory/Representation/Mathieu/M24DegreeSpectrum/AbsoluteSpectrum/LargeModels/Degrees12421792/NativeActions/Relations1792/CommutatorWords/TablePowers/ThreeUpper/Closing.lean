module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.ThreeSixthWideTables
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Identity

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.Closing.Rows00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.Closing.Rows01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.Closing.Rows02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.Closing.Rows03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.Closing.Rows04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.Closing.Rows05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.Closing.Rows06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper.Closing.Rows07
/-!
# Complete literal threeSixth times threeSixth certificate

Eight separately compiled row-certificate batches cover every row. The checked
radix conversion and hint alignment turn them into a full matrix equality.
All checks use kernel reduction; numeric generation supplies no proof evidence.
Source: ATLAS M24G1-P1; see `../source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper
open Arithmetic GeneratorOrders
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data

set_option Elab.async false

private theorem all_products : threeSixthTagged.flatten.map
    (rowFast 1792 32 threeSixthRows threeSixthWide) = identityRows.flatten := by
  rw [List.map_flatten]
  apply congrArg List.flatten
  change ([threeSixthTagged00.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged01.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged02.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged03.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged04.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged05.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged06.map (rowFast 1792 32 threeSixthRows threeSixthWide)] ++ [threeSixthTagged07.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged08.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged09.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged10.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged11.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged12.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged13.map (rowFast 1792 32 threeSixthRows threeSixthWide)] ++ [threeSixthTagged14.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged15.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged16.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged17.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged18.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged19.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged20.map (rowFast 1792 32 threeSixthRows threeSixthWide)] ++ [threeSixthTagged21.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged22.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged23.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged24.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged25.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged26.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged27.map (rowFast 1792 32 threeSixthRows threeSixthWide)] ++ [threeSixthTagged28.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged29.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged30.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged31.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged32.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged33.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged34.map (rowFast 1792 32 threeSixthRows threeSixthWide)] ++ [threeSixthTagged35.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged36.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged37.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged38.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged39.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged40.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged41.map (rowFast 1792 32 threeSixthRows threeSixthWide)] ++ [threeSixthTagged42.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged43.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged44.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged45.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged46.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged47.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged48.map (rowFast 1792 32 threeSixthRows threeSixthWide)] ++ [threeSixthTagged49.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged50.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged51.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged52.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged53.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged54.map (rowFast 1792 32 threeSixthRows threeSixthWide), threeSixthTagged55.map (rowFast 1792 32 threeSixthRows threeSixthWide)]) =
    ([identityRows00, identityRows01, identityRows02, identityRows03, identityRows04, identityRows05, identityRows06] ++ [identityRows07, identityRows08, identityRows09, identityRows10, identityRows11, identityRows12, identityRows13] ++ [identityRows14, identityRows15, identityRows16, identityRows17, identityRows18, identityRows19, identityRows20] ++ [identityRows21, identityRows22, identityRows23, identityRows24, identityRows25, identityRows26, identityRows27] ++ [identityRows28, identityRows29, identityRows30, identityRows31, identityRows32, identityRows33, identityRows34] ++ [identityRows35, identityRows36, identityRows37, identityRows38, identityRows39, identityRows40, identityRows41] ++ [identityRows42, identityRows43, identityRows44, identityRows45, identityRows46, identityRows47, identityRows48] ++ [identityRows49, identityRows50, identityRows51, identityRows52, identityRows53, identityRows54, identityRows55])
  rw [ClosingRows.batch00, ClosingRows.batch01, ClosingRows.batch02, ClosingRows.batch03, ClosingRows.batch04, ClosingRows.batch05, ClosingRows.batch06, ClosingRows.batch07]

/-- Every row of this fixed matrix product is certified. -/
theorem closing : threeSixth * threeSixth = identity := by
  have h := product_fast 1792 32 (by decide) (by decide) threeSixthRows threeSixthWide
    threeSixthTagged.flatten identityRows.flatten threeSixthRows_width threeSixthRows_length
    threeSixthWide_eq threeSixthTagged_length all_products
  rw [threeSixthTagged_eq] at h
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper
