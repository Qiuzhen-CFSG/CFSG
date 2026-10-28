module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck18

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative039_valid :
    actors039.filter (fun w => w != (190 : Fin 192)) = actors040 := by decide +kernel
private theorem positive039_valid :
    check compatible fixed 2048 positive039 (actors039.filter (compatible 190))
      (allMasks.filter (fixed 190)) = true := by decide +kernel
theorem tree039_valid : check compatible fixed 2048 tree039 actors039 allMasks = true := by
  rw [tree039, check, negative039_valid, tree040_valid, Bool.true_and]
  exact positive039_valid
private theorem negative038_valid :
    actors038.filter (fun w => w != (81 : Fin 192)) = actors039 := by decide +kernel
private theorem positive038_valid :
    check compatible fixed 2048 positive038 (actors038.filter (compatible 81))
      (allMasks.filter (fixed 81)) = true := by decide +kernel
theorem tree038_valid : check compatible fixed 2048 tree038 actors038 allMasks = true := by
  rw [tree038, check, negative038_valid, tree039_valid, Bool.true_and]
  exact positive038_valid
private theorem negative037_valid :
    actors037.filter (fun w => w != (169 : Fin 192)) = actors038 := by decide +kernel
private theorem positive037_valid :
    check compatible fixed 2048 positive037 (actors037.filter (compatible 169))
      (allMasks.filter (fixed 169)) = true := by decide +kernel
theorem tree037_valid : check compatible fixed 2048 tree037 actors037 allMasks = true := by
  rw [tree037, check, negative037_valid, tree038_valid, Bool.true_and]
  exact positive037_valid
private theorem negative036_valid :
    actors036.filter (fun w => w != (67 : Fin 192)) = actors037 := by decide +kernel
private theorem positive036_valid :
    check compatible fixed 2048 positive036 (actors036.filter (compatible 67))
      (allMasks.filter (fixed 67)) = true := by decide +kernel
theorem tree036_valid : check compatible fixed 2048 tree036 actors036 allMasks = true := by
  rw [tree036, check, negative036_valid, tree037_valid, Bool.true_and]
  exact positive036_valid
private theorem negative035_valid :
    actors035.filter (fun w => w != (150 : Fin 192)) = actors036 := by decide +kernel
private theorem positive035_valid :
    check compatible fixed 2048 positive035 (actors035.filter (compatible 150))
      (allMasks.filter (fixed 150)) = true := by decide +kernel
theorem tree035_valid : check compatible fixed 2048 tree035 actors035 allMasks = true := by
  rw [tree035, check, negative035_valid, tree036_valid, Bool.true_and]
  exact positive035_valid
private theorem negative034_valid :
    actors034.filter (fun w => w != (53 : Fin 192)) = actors035 := by decide +kernel
private theorem positive034_valid :
    check compatible fixed 2048 positive034 (actors034.filter (compatible 53))
      (allMasks.filter (fixed 53)) = true := by decide +kernel
theorem tree034_valid : check compatible fixed 2048 tree034 actors034 allMasks = true := by
  rw [tree034, check, negative034_valid, tree035_valid, Bool.true_and]
  exact positive034_valid
private theorem negative033_valid :
    actors033.filter (fun w => w != (21 : Fin 192)) = actors034 := by decide +kernel
private theorem positive033_valid :
    check compatible fixed 2048 positive033 (actors033.filter (compatible 21))
      (allMasks.filter (fixed 21)) = true := by decide +kernel
theorem tree033_valid : check compatible fixed 2048 tree033 actors033 allMasks = true := by
  rw [tree033, check, negative033_valid, tree034_valid, Bool.true_and]
  exact positive033_valid
private theorem negative032_valid :
    actors032.filter (fun w => w != (20 : Fin 192)) = actors033 := by decide +kernel
private theorem positive032_valid :
    check compatible fixed 2048 positive032 (actors032.filter (compatible 20))
      (allMasks.filter (fixed 20)) = true := by decide +kernel
theorem tree032_valid : check compatible fixed 2048 tree032 actors032 allMasks = true := by
  rw [tree032, check, negative032_valid, tree033_valid, Bool.true_and]
  exact positive032_valid
end Janko4.TwoRank.Finite
