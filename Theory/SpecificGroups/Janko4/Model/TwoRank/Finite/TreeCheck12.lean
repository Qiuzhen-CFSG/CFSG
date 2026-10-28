module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck11

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative095_valid :
    actors095.filter (fun w => w != (137 : Fin 192)) = actors096 := by decide +kernel
private theorem positive095_valid :
    check compatible fixed 2048 positive095 (actors095.filter (compatible 137))
      (allMasks.filter (fixed 137)) = true := by decide +kernel
theorem tree095_valid : check compatible fixed 2048 tree095 actors095 allMasks = true := by
  rw [tree095, check, negative095_valid, tree096_valid, Bool.true_and]
  exact positive095_valid
private theorem negative094_valid :
    actors094.filter (fun w => w != (135 : Fin 192)) = actors095 := by decide +kernel
private theorem positive094_valid :
    check compatible fixed 2048 positive094 (actors094.filter (compatible 135))
      (allMasks.filter (fixed 135)) = true := by decide +kernel
theorem tree094_valid : check compatible fixed 2048 tree094 actors094 allMasks = true := by
  rw [tree094, check, negative094_valid, tree095_valid, Bool.true_and]
  exact positive094_valid
private theorem negative093_valid :
    actors093.filter (fun w => w != (126 : Fin 192)) = actors094 := by decide +kernel
private theorem positive093_valid :
    check compatible fixed 2048 positive093 (actors093.filter (compatible 126))
      (allMasks.filter (fixed 126)) = true := by decide +kernel
theorem tree093_valid : check compatible fixed 2048 tree093 actors093 allMasks = true := by
  rw [tree093, check, negative093_valid, tree094_valid, Bool.true_and]
  exact positive093_valid
private theorem negative092_valid :
    actors092.filter (fun w => w != (125 : Fin 192)) = actors093 := by decide +kernel
private theorem positive092_valid :
    check compatible fixed 2048 positive092 (actors092.filter (compatible 125))
      (allMasks.filter (fixed 125)) = true := by decide +kernel
theorem tree092_valid : check compatible fixed 2048 tree092 actors092 allMasks = true := by
  rw [tree092, check, negative092_valid, tree093_valid, Bool.true_and]
  exact positive092_valid
private theorem negative091_valid :
    actors091.filter (fun w => w != (83 : Fin 192)) = actors092 := by decide +kernel
private theorem positive091_valid :
    check compatible fixed 2048 positive091 (actors091.filter (compatible 83))
      (allMasks.filter (fixed 83)) = true := by decide +kernel
theorem tree091_valid : check compatible fixed 2048 tree091 actors091 allMasks = true := by
  rw [tree091, check, negative091_valid, tree092_valid, Bool.true_and]
  exact positive091_valid
private theorem negative090_valid :
    actors090.filter (fun w => w != (79 : Fin 192)) = actors091 := by decide +kernel
private theorem positive090_valid :
    check compatible fixed 2048 positive090 (actors090.filter (compatible 79))
      (allMasks.filter (fixed 79)) = true := by decide +kernel
theorem tree090_valid : check compatible fixed 2048 tree090 actors090 allMasks = true := by
  rw [tree090, check, negative090_valid, tree091_valid, Bool.true_and]
  exact positive090_valid
private theorem negative089_valid :
    actors089.filter (fun w => w != (77 : Fin 192)) = actors090 := by decide +kernel
private theorem positive089_valid :
    check compatible fixed 2048 positive089 (actors089.filter (compatible 77))
      (allMasks.filter (fixed 77)) = true := by decide +kernel
theorem tree089_valid : check compatible fixed 2048 tree089 actors089 allMasks = true := by
  rw [tree089, check, negative089_valid, tree090_valid, Bool.true_and]
  exact positive089_valid
private theorem negative088_valid :
    actors088.filter (fun w => w != (166 : Fin 192)) = actors089 := by decide +kernel
private theorem positive088_valid :
    check compatible fixed 2048 positive088 (actors088.filter (compatible 166))
      (allMasks.filter (fixed 166)) = true := by decide +kernel
theorem tree088_valid : check compatible fixed 2048 tree088 actors088 allMasks = true := by
  rw [tree088, check, negative088_valid, tree089_valid, Bool.true_and]
  exact positive088_valid
end Janko4.TwoRank.Finite
