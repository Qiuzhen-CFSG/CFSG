module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck05

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative143_valid :
    actors143.filter (fun w => w != (151 : Fin 192)) = actors144 := by decide +kernel
private theorem positive143_valid :
    check compatible fixed 2048 positive143 (actors143.filter (compatible 151))
      (allMasks.filter (fixed 151)) = true := by decide +kernel
theorem tree143_valid : check compatible fixed 2048 tree143 actors143 allMasks = true := by
  rw [tree143, check, negative143_valid, tree144_valid, Bool.true_and]
  exact positive143_valid
private theorem negative142_valid :
    actors142.filter (fun w => w != (136 : Fin 192)) = actors143 := by decide +kernel
private theorem positive142_valid :
    check compatible fixed 2048 positive142 (actors142.filter (compatible 136))
      (allMasks.filter (fixed 136)) = true := by decide +kernel
theorem tree142_valid : check compatible fixed 2048 tree142 actors142 allMasks = true := by
  rw [tree142, check, negative142_valid, tree143_valid, Bool.true_and]
  exact positive142_valid
private theorem negative141_valid :
    actors141.filter (fun w => w != (132 : Fin 192)) = actors142 := by decide +kernel
private theorem positive141_valid :
    check compatible fixed 2048 positive141 (actors141.filter (compatible 132))
      (allMasks.filter (fixed 132)) = true := by decide +kernel
theorem tree141_valid : check compatible fixed 2048 tree141 actors141 allMasks = true := by
  rw [tree141, check, negative141_valid, tree142_valid, Bool.true_and]
  exact positive141_valid
private theorem negative140_valid :
    actors140.filter (fun w => w != (127 : Fin 192)) = actors141 := by decide +kernel
private theorem positive140_valid :
    check compatible fixed 2048 positive140 (actors140.filter (compatible 127))
      (allMasks.filter (fixed 127)) = true := by decide +kernel
theorem tree140_valid : check compatible fixed 2048 tree140 actors140 allMasks = true := by
  rw [tree140, check, negative140_valid, tree141_valid, Bool.true_and]
  exact positive140_valid
private theorem negative139_valid :
    actors139.filter (fun w => w != (23 : Fin 192)) = actors140 := by decide +kernel
private theorem positive139_valid :
    check compatible fixed 2048 positive139 (actors139.filter (compatible 23))
      (allMasks.filter (fixed 23)) = true := by decide +kernel
theorem tree139_valid : check compatible fixed 2048 tree139 actors139 allMasks = true := by
  rw [tree139, check, negative139_valid, tree140_valid, Bool.true_and]
  exact positive139_valid
private theorem negative138_valid :
    actors138.filter (fun w => w != (22 : Fin 192)) = actors139 := by decide +kernel
private theorem positive138_valid :
    check compatible fixed 2048 positive138 (actors138.filter (compatible 22))
      (allMasks.filter (fixed 22)) = true := by decide +kernel
theorem tree138_valid : check compatible fixed 2048 tree138 actors138 allMasks = true := by
  rw [tree138, check, negative138_valid, tree139_valid, Bool.true_and]
  exact positive138_valid
private theorem negative137_valid :
    actors137.filter (fun w => w != (60 : Fin 192)) = actors138 := by decide +kernel
private theorem positive137_valid :
    check compatible fixed 2048 positive137 (actors137.filter (compatible 60))
      (allMasks.filter (fixed 60)) = true := by decide +kernel
theorem tree137_valid : check compatible fixed 2048 tree137 actors137 allMasks = true := by
  rw [tree137, check, negative137_valid, tree138_valid, Bool.true_and]
  exact positive137_valid
private theorem negative136_valid :
    actors136.filter (fun w => w != (82 : Fin 192)) = actors137 := by decide +kernel
private theorem positive136_valid :
    check compatible fixed 2048 positive136 (actors136.filter (compatible 82))
      (allMasks.filter (fixed 82)) = true := by decide +kernel
theorem tree136_valid : check compatible fixed 2048 tree136 actors136 allMasks = true := by
  rw [tree136, check, negative136_valid, tree137_valid, Bool.true_and]
  exact positive136_valid
end Janko4.TwoRank.Finite
