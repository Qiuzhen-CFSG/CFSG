module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck07

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative127_valid :
    actors127.filter (fun w => w != (47 : Fin 192)) = actors128 := by decide +kernel
private theorem positive127_valid :
    check compatible fixed 2048 positive127 (actors127.filter (compatible 47))
      (allMasks.filter (fixed 47)) = true := by decide +kernel
theorem tree127_valid : check compatible fixed 2048 tree127 actors127 allMasks = true := by
  rw [tree127, check, negative127_valid, tree128_valid, Bool.true_and]
  exact positive127_valid
private theorem negative126_valid :
    actors126.filter (fun w => w != (121 : Fin 192)) = actors127 := by decide +kernel
private theorem positive126_valid :
    check compatible fixed 2048 positive126 (actors126.filter (compatible 121))
      (allMasks.filter (fixed 121)) = true := by decide +kernel
theorem tree126_valid : check compatible fixed 2048 tree126 actors126 allMasks = true := by
  rw [tree126, check, negative126_valid, tree127_valid, Bool.true_and]
  exact positive126_valid
private theorem negative125_valid :
    actors125.filter (fun w => w != (40 : Fin 192)) = actors126 := by decide +kernel
private theorem positive125_valid :
    check compatible fixed 2048 positive125 (actors125.filter (compatible 40))
      (allMasks.filter (fixed 40)) = true := by decide +kernel
theorem tree125_valid : check compatible fixed 2048 tree125 actors125 allMasks = true := by
  rw [tree125, check, negative125_valid, tree126_valid, Bool.true_and]
  exact positive125_valid
private theorem negative124_valid :
    actors124.filter (fun w => w != (35 : Fin 192)) = actors125 := by decide +kernel
private theorem positive124_valid :
    check compatible fixed 2048 positive124 (actors124.filter (compatible 35))
      (allMasks.filter (fixed 35)) = true := by decide +kernel
theorem tree124_valid : check compatible fixed 2048 tree124 actors124 allMasks = true := by
  rw [tree124, check, negative124_valid, tree125_valid, Bool.true_and]
  exact positive124_valid
private theorem negative123_valid :
    actors123.filter (fun w => w != (31 : Fin 192)) = actors124 := by decide +kernel
private theorem positive123_valid :
    check compatible fixed 2048 positive123 (actors123.filter (compatible 31))
      (allMasks.filter (fixed 31)) = true := by decide +kernel
theorem tree123_valid : check compatible fixed 2048 tree123 actors123 allMasks = true := by
  rw [tree123, check, negative123_valid, tree124_valid, Bool.true_and]
  exact positive123_valid
private theorem negative122_valid :
    actors122.filter (fun w => w != (30 : Fin 192)) = actors123 := by decide +kernel
private theorem positive122_valid :
    check compatible fixed 2048 positive122 (actors122.filter (compatible 30))
      (allMasks.filter (fixed 30)) = true := by decide +kernel
theorem tree122_valid : check compatible fixed 2048 tree122 actors122 allMasks = true := by
  rw [tree122, check, negative122_valid, tree123_valid, Bool.true_and]
  exact positive122_valid
private theorem negative121_valid :
    actors121.filter (fun w => w != (28 : Fin 192)) = actors122 := by decide +kernel
private theorem positive121_valid :
    check compatible fixed 2048 positive121 (actors121.filter (compatible 28))
      (allMasks.filter (fixed 28)) = true := by decide +kernel
theorem tree121_valid : check compatible fixed 2048 tree121 actors121 allMasks = true := by
  rw [tree121, check, negative121_valid, tree122_valid, Bool.true_and]
  exact positive121_valid
private theorem negative120_valid :
    actors120.filter (fun w => w != (26 : Fin 192)) = actors121 := by decide +kernel
private theorem positive120_valid :
    check compatible fixed 2048 positive120 (actors120.filter (compatible 26))
      (allMasks.filter (fixed 26)) = true := by decide +kernel
theorem tree120_valid : check compatible fixed 2048 tree120 actors120 allMasks = true := by
  rw [tree120, check, negative120_valid, tree121_valid, Bool.true_and]
  exact positive120_valid
end Janko4.TwoRank.Finite
