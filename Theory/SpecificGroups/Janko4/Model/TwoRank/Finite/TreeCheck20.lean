module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck19

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative031_valid :
    actors031.filter (fun w => w != (38 : Fin 192)) = actors032 := by decide +kernel
private theorem positive031_valid :
    check compatible fixed 2048 positive031 (actors031.filter (compatible 38))
      (allMasks.filter (fixed 38)) = true := by decide +kernel
theorem tree031_valid : check compatible fixed 2048 tree031 actors031 allMasks = true := by
  rw [tree031, check, negative031_valid, tree032_valid, Bool.true_and]
  exact positive031_valid
private theorem negative030_valid :
    actors030.filter (fun w => w != (36 : Fin 192)) = actors031 := by decide +kernel
private theorem positive030_valid :
    check compatible fixed 2048 positive030 (actors030.filter (compatible 36))
      (allMasks.filter (fixed 36)) = true := by decide +kernel
theorem tree030_valid : check compatible fixed 2048 tree030 actors030 allMasks = true := by
  rw [tree030, check, negative030_valid, tree031_valid, Bool.true_and]
  exact positive030_valid
private theorem negative029_valid :
    actors029.filter (fun w => w != (116 : Fin 192)) = actors030 := by decide +kernel
private theorem positive029_valid :
    check compatible fixed 2048 positive029 (actors029.filter (compatible 116))
      (allMasks.filter (fixed 116)) = true := by decide +kernel
theorem tree029_valid : check compatible fixed 2048 tree029 actors029 allMasks = true := by
  rw [tree029, check, negative029_valid, tree030_valid, Bool.true_and]
  exact positive029_valid
private theorem negative028_valid :
    actors028.filter (fun w => w != (114 : Fin 192)) = actors029 := by decide +kernel
private theorem positive028_valid :
    check compatible fixed 2048 positive028 (actors028.filter (compatible 114))
      (allMasks.filter (fixed 114)) = true := by decide +kernel
theorem tree028_valid : check compatible fixed 2048 tree028 actors028 allMasks = true := by
  rw [tree028, check, negative028_valid, tree029_valid, Bool.true_and]
  exact positive028_valid
private theorem negative027_valid :
    actors027.filter (fun w => w != (105 : Fin 192)) = actors028 := by decide +kernel
private theorem positive027_valid :
    check compatible fixed 2048 positive027 (actors027.filter (compatible 105))
      (allMasks.filter (fixed 105)) = true := by decide +kernel
theorem tree027_valid : check compatible fixed 2048 tree027 actors027 allMasks = true := by
  rw [tree027, check, negative027_valid, tree028_valid, Bool.true_and]
  exact positive027_valid
private theorem negative026_valid :
    actors026.filter (fun w => w != (104 : Fin 192)) = actors027 := by decide +kernel
private theorem positive026_valid :
    check compatible fixed 2048 positive026 (actors026.filter (compatible 104))
      (allMasks.filter (fixed 104)) = true := by decide +kernel
theorem tree026_valid : check compatible fixed 2048 tree026 actors026 allMasks = true := by
  rw [tree026, check, negative026_valid, tree027_valid, Bool.true_and]
  exact positive026_valid
private theorem negative025_valid :
    actors025.filter (fun w => w != (95 : Fin 192)) = actors026 := by decide +kernel
private theorem positive025_valid :
    check compatible fixed 2048 positive025 (actors025.filter (compatible 95))
      (allMasks.filter (fixed 95)) = true := by decide +kernel
theorem tree025_valid : check compatible fixed 2048 tree025 actors025 allMasks = true := by
  rw [tree025, check, negative025_valid, tree026_valid, Bool.true_and]
  exact positive025_valid
private theorem negative024_valid :
    actors024.filter (fun w => w != (92 : Fin 192)) = actors025 := by decide +kernel
private theorem positive024_valid :
    check compatible fixed 2048 positive024 (actors024.filter (compatible 92))
      (allMasks.filter (fixed 92)) = true := by decide +kernel
theorem tree024_valid : check compatible fixed 2048 tree024 actors024 allMasks = true := by
  rw [tree024, check, negative024_valid, tree025_valid, Bool.true_and]
  exact positive024_valid
end Janko4.TwoRank.Finite
