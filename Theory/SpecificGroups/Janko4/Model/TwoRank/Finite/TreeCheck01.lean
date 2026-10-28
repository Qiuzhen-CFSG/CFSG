module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck00

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative183_valid :
    actors183.filter (fun w => w != (37 : Fin 192)) = actors184 := by decide +kernel
private theorem positive183_valid :
    check compatible fixed 2048 positive183 (actors183.filter (compatible 37))
      (allMasks.filter (fixed 37)) = true := by decide +kernel
theorem tree183_valid : check compatible fixed 2048 tree183 actors183 allMasks = true := by
  rw [tree183, check, negative183_valid, tree184_valid, Bool.true_and]
  exact positive183_valid
private theorem negative182_valid :
    actors182.filter (fun w => w != (16 : Fin 192)) = actors183 := by decide +kernel
private theorem positive182_valid :
    check compatible fixed 2048 positive182 (actors182.filter (compatible 16))
      (allMasks.filter (fixed 16)) = true := by decide +kernel
theorem tree182_valid : check compatible fixed 2048 tree182 actors182 allMasks = true := by
  rw [tree182, check, negative182_valid, tree183_valid, Bool.true_and]
  exact positive182_valid
private theorem negative181_valid :
    actors181.filter (fun w => w != (108 : Fin 192)) = actors182 := by decide +kernel
private theorem positive181_valid :
    check compatible fixed 2048 positive181 (actors181.filter (compatible 108))
      (allMasks.filter (fixed 108)) = true := by decide +kernel
theorem tree181_valid : check compatible fixed 2048 tree181 actors181 allMasks = true := by
  rw [tree181, check, negative181_valid, tree182_valid, Bool.true_and]
  exact positive181_valid
private theorem negative180_valid :
    actors180.filter (fun w => w != (93 : Fin 192)) = actors181 := by decide +kernel
private theorem positive180_valid :
    check compatible fixed 2048 positive180 (actors180.filter (compatible 93))
      (allMasks.filter (fixed 93)) = true := by decide +kernel
theorem tree180_valid : check compatible fixed 2048 tree180 actors180 allMasks = true := by
  rw [tree180, check, negative180_valid, tree181_valid, Bool.true_and]
  exact positive180_valid
private theorem negative179_valid :
    actors179.filter (fun w => w != (107 : Fin 192)) = actors180 := by decide +kernel
private theorem positive179_valid :
    check compatible fixed 2048 positive179 (actors179.filter (compatible 107))
      (allMasks.filter (fixed 107)) = true := by decide +kernel
theorem tree179_valid : check compatible fixed 2048 tree179 actors179 allMasks = true := by
  rw [tree179, check, negative179_valid, tree180_valid, Bool.true_and]
  exact positive179_valid
private theorem negative178_valid :
    actors178.filter (fun w => w != (106 : Fin 192)) = actors179 := by decide +kernel
private theorem positive178_valid :
    check compatible fixed 2048 positive178 (actors178.filter (compatible 106))
      (allMasks.filter (fixed 106)) = true := by decide +kernel
theorem tree178_valid : check compatible fixed 2048 tree178 actors178 allMasks = true := by
  rw [tree178, check, negative178_valid, tree179_valid, Bool.true_and]
  exact positive178_valid
private theorem negative177_valid :
    actors177.filter (fun w => w != (24 : Fin 192)) = actors178 := by decide +kernel
private theorem positive177_valid :
    check compatible fixed 2048 positive177 (actors177.filter (compatible 24))
      (allMasks.filter (fixed 24)) = true := by decide +kernel
theorem tree177_valid : check compatible fixed 2048 tree177 actors177 allMasks = true := by
  rw [tree177, check, negative177_valid, tree178_valid, Bool.true_and]
  exact positive177_valid
private theorem negative176_valid :
    actors176.filter (fun w => w != (68 : Fin 192)) = actors177 := by decide +kernel
private theorem positive176_valid :
    check compatible fixed 2048 positive176 (actors176.filter (compatible 68))
      (allMasks.filter (fixed 68)) = true := by decide +kernel
theorem tree176_valid : check compatible fixed 2048 tree176 actors176 allMasks = true := by
  rw [tree176, check, negative176_valid, tree177_valid, Bool.true_and]
  exact positive176_valid
end Janko4.TwoRank.Finite
