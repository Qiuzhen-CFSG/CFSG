module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck02

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative167_valid :
    actors167.filter (fun w => w != (171 : Fin 192)) = actors168 := by decide +kernel
private theorem positive167_valid :
    check compatible fixed 2048 positive167 (actors167.filter (compatible 171))
      (allMasks.filter (fixed 171)) = true := by decide +kernel
theorem tree167_valid : check compatible fixed 2048 tree167 actors167 allMasks = true := by
  rw [tree167, check, negative167_valid, tree168_valid, Bool.true_and]
  exact positive167_valid
private theorem negative166_valid :
    actors166.filter (fun w => w != (101 : Fin 192)) = actors167 := by decide +kernel
private theorem positive166_valid :
    check compatible fixed 2048 positive166 (actors166.filter (compatible 101))
      (allMasks.filter (fixed 101)) = true := by decide +kernel
theorem tree166_valid : check compatible fixed 2048 tree166 actors166 allMasks = true := by
  rw [tree166, check, negative166_valid, tree167_valid, Bool.true_and]
  exact positive166_valid
private theorem negative165_valid :
    actors165.filter (fun w => w != (156 : Fin 192)) = actors166 := by decide +kernel
private theorem positive165_valid :
    check compatible fixed 2048 positive165 (actors165.filter (compatible 156))
      (allMasks.filter (fixed 156)) = true := by decide +kernel
theorem tree165_valid : check compatible fixed 2048 tree165 actors165 allMasks = true := by
  rw [tree165, check, negative165_valid, tree166_valid, Bool.true_and]
  exact positive165_valid
private theorem negative164_valid :
    actors164.filter (fun w => w != (61 : Fin 192)) = actors165 := by decide +kernel
private theorem positive164_valid :
    check compatible fixed 2048 positive164 (actors164.filter (compatible 61))
      (allMasks.filter (fixed 61)) = true := by decide +kernel
theorem tree164_valid : check compatible fixed 2048 tree164 actors164 allMasks = true := by
  rw [tree164, check, negative164_valid, tree165_valid, Bool.true_and]
  exact positive164_valid
private theorem negative163_valid :
    actors163.filter (fun w => w != (152 : Fin 192)) = actors164 := by decide +kernel
private theorem positive163_valid :
    check compatible fixed 2048 positive163 (actors163.filter (compatible 152))
      (allMasks.filter (fixed 152)) = true := by decide +kernel
theorem tree163_valid : check compatible fixed 2048 tree163 actors163 allMasks = true := by
  rw [tree163, check, negative163_valid, tree164_valid, Bool.true_and]
  exact positive163_valid
private theorem negative162_valid :
    actors162.filter (fun w => w != (19 : Fin 192)) = actors163 := by decide +kernel
private theorem positive162_valid :
    check compatible fixed 2048 positive162 (actors162.filter (compatible 19))
      (allMasks.filter (fixed 19)) = true := by decide +kernel
theorem tree162_valid : check compatible fixed 2048 tree162 actors162 allMasks = true := by
  rw [tree162, check, negative162_valid, tree163_valid, Bool.true_and]
  exact positive162_valid
private theorem negative161_valid :
    actors161.filter (fun w => w != (188 : Fin 192)) = actors162 := by decide +kernel
private theorem positive161_valid :
    check compatible fixed 2048 positive161 (actors161.filter (compatible 188))
      (allMasks.filter (fixed 188)) = true := by decide +kernel
theorem tree161_valid : check compatible fixed 2048 tree161 actors161 allMasks = true := by
  rw [tree161, check, negative161_valid, tree162_valid, Bool.true_and]
  exact positive161_valid
private theorem negative160_valid :
    actors160.filter (fun w => w != (91 : Fin 192)) = actors161 := by decide +kernel
private theorem positive160_valid :
    check compatible fixed 2048 positive160 (actors160.filter (compatible 91))
      (allMasks.filter (fixed 91)) = true := by decide +kernel
theorem tree160_valid : check compatible fixed 2048 tree160 actors160 allMasks = true := by
  rw [tree160, check, negative160_valid, tree161_valid, Bool.true_and]
  exact positive160_valid
end Janko4.TwoRank.Finite
