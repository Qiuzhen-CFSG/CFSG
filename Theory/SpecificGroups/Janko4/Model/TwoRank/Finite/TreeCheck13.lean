module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck12

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative087_valid :
    actors087.filter (fun w => w != (165 : Fin 192)) = actors088 := by decide +kernel
private theorem positive087_valid :
    check compatible fixed 2048 positive087 (actors087.filter (compatible 165))
      (allMasks.filter (fixed 165)) = true := by decide +kernel
theorem tree087_valid : check compatible fixed 2048 tree087 actors087 allMasks = true := by
  rw [tree087, check, negative087_valid, tree088_valid, Bool.true_and]
  exact positive087_valid
private theorem negative086_valid :
    actors086.filter (fun w => w != (164 : Fin 192)) = actors087 := by decide +kernel
private theorem positive086_valid :
    check compatible fixed 2048 positive086 (actors086.filter (compatible 164))
      (allMasks.filter (fixed 164)) = true := by decide +kernel
theorem tree086_valid : check compatible fixed 2048 tree086 actors086 allMasks = true := by
  rw [tree086, check, negative086_valid, tree087_valid, Bool.true_and]
  exact positive086_valid
private theorem negative085_valid :
    actors085.filter (fun w => w != (163 : Fin 192)) = actors086 := by decide +kernel
private theorem positive085_valid :
    check compatible fixed 2048 positive085 (actors085.filter (compatible 163))
      (allMasks.filter (fixed 163)) = true := by decide +kernel
theorem tree085_valid : check compatible fixed 2048 tree085 actors085 allMasks = true := by
  rw [tree085, check, negative085_valid, tree086_valid, Bool.true_and]
  exact positive085_valid
private theorem negative084_valid :
    actors084.filter (fun w => w != (162 : Fin 192)) = actors085 := by decide +kernel
private theorem positive084_valid :
    check compatible fixed 2048 positive084 (actors084.filter (compatible 162))
      (allMasks.filter (fixed 162)) = true := by decide +kernel
theorem tree084_valid : check compatible fixed 2048 tree084 actors084 allMasks = true := by
  rw [tree084, check, negative084_valid, tree085_valid, Bool.true_and]
  exact positive084_valid
private theorem negative083_valid :
    actors083.filter (fun w => w != (161 : Fin 192)) = actors084 := by decide +kernel
private theorem positive083_valid :
    check compatible fixed 2048 positive083 (actors083.filter (compatible 161))
      (allMasks.filter (fixed 161)) = true := by decide +kernel
theorem tree083_valid : check compatible fixed 2048 tree083 actors083 allMasks = true := by
  rw [tree083, check, negative083_valid, tree084_valid, Bool.true_and]
  exact positive083_valid
private theorem negative082_valid :
    actors082.filter (fun w => w != (159 : Fin 192)) = actors083 := by decide +kernel
private theorem positive082_valid :
    check compatible fixed 2048 positive082 (actors082.filter (compatible 159))
      (allMasks.filter (fixed 159)) = true := by decide +kernel
theorem tree082_valid : check compatible fixed 2048 tree082 actors082 allMasks = true := by
  rw [tree082, check, negative082_valid, tree083_valid, Bool.true_and]
  exact positive082_valid
private theorem negative081_valid :
    actors081.filter (fun w => w != (158 : Fin 192)) = actors082 := by decide +kernel
private theorem positive081_valid :
    check compatible fixed 2048 positive081 (actors081.filter (compatible 158))
      (allMasks.filter (fixed 158)) = true := by decide +kernel
theorem tree081_valid : check compatible fixed 2048 tree081 actors081 allMasks = true := by
  rw [tree081, check, negative081_valid, tree082_valid, Bool.true_and]
  exact positive081_valid
private theorem negative080_valid :
    actors080.filter (fun w => w != (157 : Fin 192)) = actors081 := by decide +kernel
private theorem positive080_valid :
    check compatible fixed 2048 positive080 (actors080.filter (compatible 157))
      (allMasks.filter (fixed 157)) = true := by decide +kernel
theorem tree080_valid : check compatible fixed 2048 tree080 actors080 allMasks = true := by
  rw [tree080, check, negative080_valid, tree081_valid, Bool.true_and]
  exact positive080_valid
end Janko4.TwoRank.Finite
