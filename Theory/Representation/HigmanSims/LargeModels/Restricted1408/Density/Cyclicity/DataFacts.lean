module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ParentBounds
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowData
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnData

/-!
# Sizes and well-founded predecessors of the proposed cyclic orbits

These kernel checks certify the shape of the two proposed certificates.
Recurrence and spanning assertions are separate mathematical obligations.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity

theorem rowOrbitRows_size : rowOrbitRows.size = 1408 := by decide +kernel

theorem columnOrbitRows_size : columnOrbitRows.size = 1408 := by decide +kernel

theorem rowOrbitParents_size : rowOrbitParents.size = 1408 := by decide +kernel

theorem columnOrbitParents_size : columnOrbitParents.size = 1408 := by decide +kernel

theorem rowOrbitChoices_size : rowOrbitChoices.size = 1408 := by decide +kernel

theorem columnOrbitChoices_size : columnOrbitChoices.size = 1408 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowParents_check : parentsBefore 0 rowOrbitParents.toList = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem columnParents_check : parentsBefore 0 columnOrbitParents.toList = true := by
  decide +kernel

theorem rowOrbitParents_lt (i : Fin 1408) (hi : 0 < i.val) :
    rowOrbitParents[i.val]! < i.val := by
  have hn : i.val < rowOrbitParents.size := rowOrbitParents_size.symm ▸ i.isLt
  have h := parentsBefore_sound 0 rowOrbitParents.toList rowParents_check i.val
    (by simpa only [Array.length_toList] using hn) (by simpa only [Nat.zero_add] using hi)
  simpa only [Nat.zero_add, Array.getElem_toList, getElem!_pos rowOrbitParents i.val hn] using h

theorem columnOrbitParents_lt (i : Fin 1408) (hi : 0 < i.val) :
    columnOrbitParents[i.val]! < i.val := by
  have hn : i.val < columnOrbitParents.size := columnOrbitParents_size.symm ▸ i.isLt
  have h := parentsBefore_sound 0 columnOrbitParents.toList columnParents_check i.val
    (by simpa only [Array.length_toList] using hn) (by simpa only [Nat.zero_add] using hi)
  simpa only [Nat.zero_add, Array.getElem_toList, getElem!_pos columnOrbitParents i.val hn] using h

set_option maxRecDepth 4096 in
theorem rowOrbitRows_zero : rowOrbitRows[0]! = 6139659506272620636799992634585864912974850861989027553578679464913486302281527940175156070320392067611652369546924542021397720996761118473793348864471114369508769626501072600596880300320335650299740397691746171392531800198810740112039712369436304016295946974394247809937077352640764210711792336474238360822535962832740291840144514467706461618504933402428400203289257630659796294098578531096526360994385659558891729078815382 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem columnOrbitRows_zero : columnOrbitRows[0]! = 3037566777681267535834465479477380210446177044093850219542017719937461953016038750181753272333662566324377528990954025738249985938610247160176175638580520348176498059831193934536735574962891405363127719209003405508515098615267758094552103906262663260137666912768254730890609589573719963388200362861770965963113113402544595261017349602099599066548935105647282472801271845992658676808526609012602330107685271989261917926201689 := by
  decide +kernel

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
