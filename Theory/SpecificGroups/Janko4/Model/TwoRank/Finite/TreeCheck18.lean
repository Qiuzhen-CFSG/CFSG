module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck17

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative047_valid :
    actors047.filter (fun w => w != (119 : Fin 192)) = actors048 := by decide +kernel
private theorem positive047_valid :
    check compatible fixed 2048 positive047 (actors047.filter (compatible 119))
      (allMasks.filter (fixed 119)) = true := by decide +kernel
theorem tree047_valid : check compatible fixed 2048 tree047 actors047 allMasks = true := by
  rw [tree047, check, negative047_valid, tree048_valid, Bool.true_and]
  exact positive047_valid
private theorem negative046_valid :
    actors046.filter (fun w => w != (118 : Fin 192)) = actors047 := by decide +kernel
private theorem positive046_valid :
    check compatible fixed 2048 positive046 (actors046.filter (compatible 118))
      (allMasks.filter (fixed 118)) = true := by decide +kernel
theorem tree046_valid : check compatible fixed 2048 tree046 actors046 allMasks = true := by
  rw [tree046, check, negative046_valid, tree047_valid, Bool.true_and]
  exact positive046_valid
private theorem negative045_valid :
    actors045.filter (fun w => w != (117 : Fin 192)) = actors046 := by decide +kernel
private theorem positive045_valid :
    check compatible fixed 2048 positive045 (actors045.filter (compatible 117))
      (allMasks.filter (fixed 117)) = true := by decide +kernel
theorem tree045_valid : check compatible fixed 2048 tree045 actors045 allMasks = true := by
  rw [tree045, check, negative045_valid, tree046_valid, Bool.true_and]
  exact positive045_valid
private theorem negative044_valid :
    actors044.filter (fun w => w != (110 : Fin 192)) = actors045 := by decide +kernel
private theorem positive044_valid :
    check compatible fixed 2048 positive044 (actors044.filter (compatible 110))
      (allMasks.filter (fixed 110)) = true := by decide +kernel
theorem tree044_valid : check compatible fixed 2048 tree044 actors044 allMasks = true := by
  rw [tree044, check, negative044_valid, tree045_valid, Bool.true_and]
  exact positive044_valid
private theorem negative043_valid :
    actors043.filter (fun w => w != (109 : Fin 192)) = actors044 := by decide +kernel
private theorem positive043_valid :
    check compatible fixed 2048 positive043 (actors043.filter (compatible 109))
      (allMasks.filter (fixed 109)) = true := by decide +kernel
theorem tree043_valid : check compatible fixed 2048 tree043 actors043 allMasks = true := by
  rw [tree043, check, negative043_valid, tree044_valid, Bool.true_and]
  exact positive043_valid
private theorem negative042_valid :
    actors042.filter (fun w => w != (99 : Fin 192)) = actors043 := by decide +kernel
private theorem positive042_valid :
    check compatible fixed 2048 positive042 (actors042.filter (compatible 99))
      (allMasks.filter (fixed 99)) = true := by decide +kernel
theorem tree042_valid : check compatible fixed 2048 tree042 actors042 allMasks = true := by
  rw [tree042, check, negative042_valid, tree043_valid, Bool.true_and]
  exact positive042_valid
private theorem negative041_valid :
    actors041.filter (fun w => w != (98 : Fin 192)) = actors042 := by decide +kernel
private theorem positive041_valid :
    check compatible fixed 2048 positive041 (actors041.filter (compatible 98))
      (allMasks.filter (fixed 98)) = true := by decide +kernel
theorem tree041_valid : check compatible fixed 2048 tree041 actors041 allMasks = true := by
  rw [tree041, check, negative041_valid, tree042_valid, Bool.true_and]
  exact positive041_valid
private theorem negative040_valid :
    actors040.filter (fun w => w != (94 : Fin 192)) = actors041 := by decide +kernel
private theorem positive040_valid :
    check compatible fixed 2048 positive040 (actors040.filter (compatible 94))
      (allMasks.filter (fixed 94)) = true := by decide +kernel
theorem tree040_valid : check compatible fixed 2048 tree040 actors040 allMasks = true := by
  rw [tree040, check, negative040_valid, tree041_valid, Bool.true_and]
  exact positive040_valid
end Janko4.TwoRank.Finite
