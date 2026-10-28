module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck22

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative007_valid :
    actors007.filter (fun w => w != (183 : Fin 192)) = actors008 := by decide +kernel
private theorem positive007_valid :
    check compatible fixed 2048 positive007 (actors007.filter (compatible 183))
      (allMasks.filter (fixed 183)) = true := by decide +kernel
theorem tree007_valid : check compatible fixed 2048 tree007 actors007 allMasks = true := by
  rw [tree007, check, negative007_valid, tree008_valid, Bool.true_and]
  exact positive007_valid
private theorem negative006_valid :
    actors006.filter (fun w => w != (182 : Fin 192)) = actors007 := by decide +kernel
private theorem positive006_valid :
    check compatible fixed 2048 positive006 (actors006.filter (compatible 182))
      (allMasks.filter (fixed 182)) = true := by decide +kernel
theorem tree006_valid : check compatible fixed 2048 tree006 actors006 allMasks = true := by
  rw [tree006, check, negative006_valid, tree007_valid, Bool.true_and]
  exact positive006_valid
private theorem negative005_valid :
    actors005.filter (fun w => w != (176 : Fin 192)) = actors006 := by decide +kernel
private theorem positive005_valid :
    check compatible fixed 2048 positive005 (actors005.filter (compatible 176))
      (allMasks.filter (fixed 176)) = true := by decide +kernel
theorem tree005_valid : check compatible fixed 2048 tree005 actors005 allMasks = true := by
  rw [tree005, check, negative005_valid, tree006_valid, Bool.true_and]
  exact positive005_valid
private theorem negative004_valid :
    actors004.filter (fun w => w != (123 : Fin 192)) = actors005 := by decide +kernel
private theorem positive004_valid :
    check compatible fixed 2048 positive004 (actors004.filter (compatible 123))
      (allMasks.filter (fixed 123)) = true := by decide +kernel
theorem tree004_valid : check compatible fixed 2048 tree004 actors004 allMasks = true := by
  rw [tree004, check, negative004_valid, tree005_valid, Bool.true_and]
  exact positive004_valid
private theorem negative003_valid :
    actors003.filter (fun w => w != (29 : Fin 192)) = actors004 := by decide +kernel
private theorem positive003_valid :
    check compatible fixed 2048 positive003 (actors003.filter (compatible 29))
      (allMasks.filter (fixed 29)) = true := by decide +kernel
theorem tree003_valid : check compatible fixed 2048 tree003 actors003 allMasks = true := by
  rw [tree003, check, negative003_valid, tree004_valid, Bool.true_and]
  exact positive003_valid
private theorem negative002_valid :
    actors002.filter (fun w => w != (11 : Fin 192)) = actors003 := by decide +kernel
private theorem positive002_valid :
    check compatible fixed 2048 positive002 (actors002.filter (compatible 11))
      (allMasks.filter (fixed 11)) = true := by decide +kernel
theorem tree002_valid : check compatible fixed 2048 tree002 actors002 allMasks = true := by
  rw [tree002, check, negative002_valid, tree003_valid, Bool.true_and]
  exact positive002_valid
private theorem negative001_valid :
    actors001.filter (fun w => w != (5 : Fin 192)) = actors002 := by decide +kernel
private theorem positive001_valid :
    check compatible fixed 2048 positive001 (actors001.filter (compatible 5))
      (allMasks.filter (fixed 5)) = true := by decide +kernel
theorem tree001_valid : check compatible fixed 2048 tree001 actors001 allMasks = true := by
  rw [tree001, check, negative001_valid, tree002_valid, Bool.true_and]
  exact positive001_valid
private theorem negative000_valid :
    actors000.filter (fun w => w != (2 : Fin 192)) = actors001 := by decide +kernel
private theorem positive000_valid :
    check compatible fixed 2048 positive000 (actors000.filter (compatible 2))
      (allMasks.filter (fixed 2)) = true := by decide +kernel
theorem tree000_valid : check compatible fixed 2048 tree000 actors000 allMasks = true := by
  rw [tree000, check, negative000_valid, tree001_valid, Bool.true_and]
  exact positive000_valid
end Janko4.TwoRank.Finite
