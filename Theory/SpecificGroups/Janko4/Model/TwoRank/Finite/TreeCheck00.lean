module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeData

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
theorem tree191_valid : check compatible fixed 2048 tree191 actors191 allMasks = true := by decide +kernel
private theorem negative190_valid :
    actors190.filter (fun w => w != (97 : Fin 192)) = actors191 := by decide +kernel
private theorem positive190_valid :
    check compatible fixed 2048 positive190 (actors190.filter (compatible 97))
      (allMasks.filter (fixed 97)) = true := by decide +kernel
theorem tree190_valid : check compatible fixed 2048 tree190 actors190 allMasks = true := by
  rw [tree190, check, negative190_valid, tree191_valid, Bool.true_and]
  exact positive190_valid
private theorem negative189_valid :
    actors189.filter (fun w => w != (17 : Fin 192)) = actors190 := by decide +kernel
private theorem positive189_valid :
    check compatible fixed 2048 positive189 (actors189.filter (compatible 17))
      (allMasks.filter (fixed 17)) = true := by decide +kernel
theorem tree189_valid : check compatible fixed 2048 tree189 actors189 allMasks = true := by
  rw [tree189, check, negative189_valid, tree190_valid, Bool.true_and]
  exact positive189_valid
private theorem negative188_valid :
    actors188.filter (fun w => w != (187 : Fin 192)) = actors189 := by decide +kernel
private theorem positive188_valid :
    check compatible fixed 2048 positive188 (actors188.filter (compatible 187))
      (allMasks.filter (fixed 187)) = true := by decide +kernel
theorem tree188_valid : check compatible fixed 2048 tree188 actors188 allMasks = true := by
  rw [tree188, check, negative188_valid, tree189_valid, Bool.true_and]
  exact positive188_valid
private theorem negative187_valid :
    actors187.filter (fun w => w != (122 : Fin 192)) = actors188 := by decide +kernel
private theorem positive187_valid :
    check compatible fixed 2048 positive187 (actors187.filter (compatible 122))
      (allMasks.filter (fixed 122)) = true := by decide +kernel
theorem tree187_valid : check compatible fixed 2048 tree187 actors187 allMasks = true := by
  rw [tree187, check, negative187_valid, tree188_valid, Bool.true_and]
  exact positive187_valid
private theorem negative186_valid :
    actors186.filter (fun w => w != (146 : Fin 192)) = actors187 := by decide +kernel
private theorem positive186_valid :
    check compatible fixed 2048 positive186 (actors186.filter (compatible 146))
      (allMasks.filter (fixed 146)) = true := by decide +kernel
theorem tree186_valid : check compatible fixed 2048 tree186 actors186 allMasks = true := by
  rw [tree186, check, negative186_valid, tree187_valid, Bool.true_and]
  exact positive186_valid
private theorem negative185_valid :
    actors185.filter (fun w => w != (80 : Fin 192)) = actors186 := by decide +kernel
private theorem positive185_valid :
    check compatible fixed 2048 positive185 (actors185.filter (compatible 80))
      (allMasks.filter (fixed 80)) = true := by decide +kernel
theorem tree185_valid : check compatible fixed 2048 tree185 actors185 allMasks = true := by
  rw [tree185, check, negative185_valid, tree186_valid, Bool.true_and]
  exact positive185_valid
private theorem negative184_valid :
    actors184.filter (fun w => w != (39 : Fin 192)) = actors185 := by decide +kernel
private theorem positive184_valid :
    check compatible fixed 2048 positive184 (actors184.filter (compatible 39))
      (allMasks.filter (fixed 39)) = true := by decide +kernel
theorem tree184_valid : check compatible fixed 2048 tree184 actors184 allMasks = true := by
  rw [tree184, check, negative184_valid, tree185_valid, Bool.true_and]
  exact positive184_valid
end Janko4.TwoRank.Finite
