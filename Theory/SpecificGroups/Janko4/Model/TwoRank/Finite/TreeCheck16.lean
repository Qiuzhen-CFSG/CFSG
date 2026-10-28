module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck15

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative063_valid :
    actors063.filter (fun w => w != (168 : Fin 192)) = actors064 := by decide +kernel
private theorem positive063_valid :
    check compatible fixed 2048 positive063 (actors063.filter (compatible 168))
      (allMasks.filter (fixed 168)) = true := by decide +kernel
theorem tree063_valid : check compatible fixed 2048 tree063 actors063 allMasks = true := by
  rw [tree063, check, negative063_valid, tree064_valid, Bool.true_and]
  exact positive063_valid
private theorem negative062_valid :
    actors062.filter (fun w => w != (167 : Fin 192)) = actors063 := by decide +kernel
private theorem positive062_valid :
    check compatible fixed 2048 positive062 (actors062.filter (compatible 167))
      (allMasks.filter (fixed 167)) = true := by decide +kernel
theorem tree062_valid : check compatible fixed 2048 tree062 actors062 allMasks = true := by
  rw [tree062, check, negative062_valid, tree063_valid, Bool.true_and]
  exact positive062_valid
private theorem negative061_valid :
    actors061.filter (fun w => w != (111 : Fin 192)) = actors062 := by decide +kernel
private theorem positive061_valid :
    check compatible fixed 2048 positive061 (actors061.filter (compatible 111))
      (allMasks.filter (fixed 111)) = true := by decide +kernel
theorem tree061_valid : check compatible fixed 2048 tree061 actors061 allMasks = true := by
  rw [tree061, check, negative061_valid, tree062_valid, Bool.true_and]
  exact positive061_valid
private theorem negative060_valid :
    actors060.filter (fun w => w != (27 : Fin 192)) = actors061 := by decide +kernel
private theorem positive060_valid :
    check compatible fixed 2048 positive060 (actors060.filter (compatible 27))
      (allMasks.filter (fixed 27)) = true := by decide +kernel
theorem tree060_valid : check compatible fixed 2048 tree060 actors060 allMasks = true := by
  rw [tree060, check, negative060_valid, tree061_valid, Bool.true_and]
  exact positive060_valid
private theorem negative059_valid :
    actors059.filter (fun w => w != (25 : Fin 192)) = actors060 := by decide +kernel
private theorem positive059_valid :
    check compatible fixed 2048 positive059 (actors059.filter (compatible 25))
      (allMasks.filter (fixed 25)) = true := by decide +kernel
theorem tree059_valid : check compatible fixed 2048 tree059 actors059 allMasks = true := by
  rw [tree059, check, negative059_valid, tree060_valid, Bool.true_and]
  exact positive059_valid
private theorem negative058_valid :
    actors058.filter (fun w => w != (96 : Fin 192)) = actors059 := by decide +kernel
private theorem positive058_valid :
    check compatible fixed 2048 positive058 (actors058.filter (compatible 96))
      (allMasks.filter (fixed 96)) = true := by decide +kernel
theorem tree058_valid : check compatible fixed 2048 tree058 actors058 allMasks = true := by
  rw [tree058, check, negative058_valid, tree059_valid, Bool.true_and]
  exact positive058_valid
private theorem negative057_valid :
    actors057.filter (fun w => w != (89 : Fin 192)) = actors058 := by decide +kernel
private theorem positive057_valid :
    check compatible fixed 2048 positive057 (actors057.filter (compatible 89))
      (allMasks.filter (fixed 89)) = true := by decide +kernel
theorem tree057_valid : check compatible fixed 2048 tree057 actors057 allMasks = true := by
  rw [tree057, check, negative057_valid, tree058_valid, Bool.true_and]
  exact positive057_valid
private theorem negative056_valid :
    actors056.filter (fun w => w != (85 : Fin 192)) = actors057 := by decide +kernel
private theorem positive056_valid :
    check compatible fixed 2048 positive056 (actors056.filter (compatible 85))
      (allMasks.filter (fixed 85)) = true := by decide +kernel
theorem tree056_valid : check compatible fixed 2048 tree056 actors056 allMasks = true := by
  rw [tree056, check, negative056_valid, tree057_valid, Bool.true_and]
  exact positive056_valid
end Janko4.TwoRank.Finite
