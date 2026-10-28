module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck13

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative079_valid :
    actors079.filter (fun w => w != (155 : Fin 192)) = actors080 := by decide +kernel
private theorem positive079_valid :
    check compatible fixed 2048 positive079 (actors079.filter (compatible 155))
      (allMasks.filter (fixed 155)) = true := by decide +kernel
theorem tree079_valid : check compatible fixed 2048 tree079 actors079 allMasks = true := by
  rw [tree079, check, negative079_valid, tree080_valid, Bool.true_and]
  exact positive079_valid
private theorem negative078_valid :
    actors078.filter (fun w => w != (154 : Fin 192)) = actors079 := by decide +kernel
private theorem positive078_valid :
    check compatible fixed 2048 positive078 (actors078.filter (compatible 154))
      (allMasks.filter (fixed 154)) = true := by decide +kernel
theorem tree078_valid : check compatible fixed 2048 tree078 actors078 allMasks = true := by
  rw [tree078, check, negative078_valid, tree079_valid, Bool.true_and]
  exact positive078_valid
private theorem negative077_valid :
    actors077.filter (fun w => w != (153 : Fin 192)) = actors078 := by decide +kernel
private theorem positive077_valid :
    check compatible fixed 2048 positive077 (actors077.filter (compatible 153))
      (allMasks.filter (fixed 153)) = true := by decide +kernel
theorem tree077_valid : check compatible fixed 2048 tree077 actors077 allMasks = true := by
  rw [tree077, check, negative077_valid, tree078_valid, Bool.true_and]
  exact positive077_valid
private theorem negative076_valid :
    actors076.filter (fun w => w != (147 : Fin 192)) = actors077 := by decide +kernel
private theorem positive076_valid :
    check compatible fixed 2048 positive076 (actors076.filter (compatible 147))
      (allMasks.filter (fixed 147)) = true := by decide +kernel
theorem tree076_valid : check compatible fixed 2048 tree076 actors076 allMasks = true := by
  rw [tree076, check, negative076_valid, tree077_valid, Bool.true_and]
  exact positive076_valid
private theorem negative075_valid :
    actors075.filter (fun w => w != (144 : Fin 192)) = actors076 := by decide +kernel
private theorem positive075_valid :
    check compatible fixed 2048 positive075 (actors075.filter (compatible 144))
      (allMasks.filter (fixed 144)) = true := by decide +kernel
theorem tree075_valid : check compatible fixed 2048 tree075 actors075 allMasks = true := by
  rw [tree075, check, negative075_valid, tree076_valid, Bool.true_and]
  exact positive075_valid
private theorem negative074_valid :
    actors074.filter (fun w => w != (143 : Fin 192)) = actors075 := by decide +kernel
private theorem positive074_valid :
    check compatible fixed 2048 positive074 (actors074.filter (compatible 143))
      (allMasks.filter (fixed 143)) = true := by decide +kernel
theorem tree074_valid : check compatible fixed 2048 tree074 actors074 allMasks = true := by
  rw [tree074, check, negative074_valid, tree075_valid, Bool.true_and]
  exact positive074_valid
private theorem negative073_valid :
    actors073.filter (fun w => w != (142 : Fin 192)) = actors074 := by decide +kernel
private theorem positive073_valid :
    check compatible fixed 2048 positive073 (actors073.filter (compatible 142))
      (allMasks.filter (fixed 142)) = true := by decide +kernel
theorem tree073_valid : check compatible fixed 2048 tree073 actors073 allMasks = true := by
  rw [tree073, check, negative073_valid, tree074_valid, Bool.true_and]
  exact positive073_valid
private theorem negative072_valid :
    actors072.filter (fun w => w != (141 : Fin 192)) = actors073 := by decide +kernel
private theorem positive072_valid :
    check compatible fixed 2048 positive072 (actors072.filter (compatible 141))
      (allMasks.filter (fixed 141)) = true := by decide +kernel
theorem tree072_valid : check compatible fixed 2048 tree072 actors072 allMasks = true := by
  rw [tree072, check, negative072_valid, tree073_valid, Bool.true_and]
  exact positive072_valid
end Janko4.TwoRank.Finite
