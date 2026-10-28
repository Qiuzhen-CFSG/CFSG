module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck08

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative119_valid :
    actors119.filter (fun w => w != (10 : Fin 192)) = actors120 := by decide +kernel
private theorem positive119_valid :
    check compatible fixed 2048 positive119 (actors119.filter (compatible 10))
      (allMasks.filter (fixed 10)) = true := by decide +kernel
theorem tree119_valid : check compatible fixed 2048 tree119 actors119 allMasks = true := by
  rw [tree119, check, negative119_valid, tree120_valid, Bool.true_and]
  exact positive119_valid
private theorem negative118_valid :
    actors118.filter (fun w => w != (9 : Fin 192)) = actors119 := by decide +kernel
private theorem positive118_valid :
    check compatible fixed 2048 positive118 (actors118.filter (compatible 9))
      (allMasks.filter (fixed 9)) = true := by decide +kernel
theorem tree118_valid : check compatible fixed 2048 tree118 actors118 allMasks = true := by
  rw [tree118, check, negative118_valid, tree119_valid, Bool.true_and]
  exact positive118_valid
private theorem negative117_valid :
    actors117.filter (fun w => w != (7 : Fin 192)) = actors118 := by decide +kernel
private theorem positive117_valid :
    check compatible fixed 2048 positive117 (actors117.filter (compatible 7))
      (allMasks.filter (fixed 7)) = true := by decide +kernel
theorem tree117_valid : check compatible fixed 2048 tree117 actors117 allMasks = true := by
  rw [tree117, check, negative117_valid, tree118_valid, Bool.true_and]
  exact positive117_valid
private theorem negative116_valid :
    actors116.filter (fun w => w != (4 : Fin 192)) = actors117 := by decide +kernel
private theorem positive116_valid :
    check compatible fixed 2048 positive116 (actors116.filter (compatible 4))
      (allMasks.filter (fixed 4)) = true := by decide +kernel
theorem tree116_valid : check compatible fixed 2048 tree116 actors116 allMasks = true := by
  rw [tree116, check, negative116_valid, tree117_valid, Bool.true_and]
  exact positive116_valid
private theorem negative115_valid :
    actors115.filter (fun w => w != (46 : Fin 192)) = actors116 := by decide +kernel
private theorem positive115_valid :
    check compatible fixed 2048 positive115 (actors115.filter (compatible 46))
      (allMasks.filter (fixed 46)) = true := by decide +kernel
theorem tree115_valid : check compatible fixed 2048 tree115 actors115 allMasks = true := by
  rw [tree115, check, negative115_valid, tree116_valid, Bool.true_and]
  exact positive115_valid
private theorem negative114_valid :
    actors114.filter (fun w => w != (45 : Fin 192)) = actors115 := by decide +kernel
private theorem positive114_valid :
    check compatible fixed 2048 positive114 (actors114.filter (compatible 45))
      (allMasks.filter (fixed 45)) = true := by decide +kernel
theorem tree114_valid : check compatible fixed 2048 tree114 actors114 allMasks = true := by
  rw [tree114, check, negative114_valid, tree115_valid, Bool.true_and]
  exact positive114_valid
private theorem negative113_valid :
    actors113.filter (fun w => w != (42 : Fin 192)) = actors114 := by decide +kernel
private theorem positive113_valid :
    check compatible fixed 2048 positive113 (actors113.filter (compatible 42))
      (allMasks.filter (fixed 42)) = true := by decide +kernel
theorem tree113_valid : check compatible fixed 2048 tree113 actors113 allMasks = true := by
  rw [tree113, check, negative113_valid, tree114_valid, Bool.true_and]
  exact positive113_valid
private theorem negative112_valid :
    actors112.filter (fun w => w != (112 : Fin 192)) = actors113 := by decide +kernel
private theorem positive112_valid :
    check compatible fixed 2048 positive112 (actors112.filter (compatible 112))
      (allMasks.filter (fixed 112)) = true := by decide +kernel
theorem tree112_valid : check compatible fixed 2048 tree112 actors112 allMasks = true := by
  rw [tree112, check, negative112_valid, tree113_valid, Bool.true_and]
  exact positive112_valid
end Janko4.TwoRank.Finite
