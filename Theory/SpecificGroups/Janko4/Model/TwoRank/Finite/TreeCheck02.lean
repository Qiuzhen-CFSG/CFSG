module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck01

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative175_valid :
    actors175.filter (fun w => w != (66 : Fin 192)) = actors176 := by decide +kernel
private theorem positive175_valid :
    check compatible fixed 2048 positive175 (actors175.filter (compatible 66))
      (allMasks.filter (fixed 66)) = true := by decide +kernel
theorem tree175_valid : check compatible fixed 2048 tree175 actors175 allMasks = true := by
  rw [tree175, check, negative175_valid, tree176_valid, Bool.true_and]
  exact positive175_valid
private theorem negative174_valid :
    actors174.filter (fun w => w != (44 : Fin 192)) = actors175 := by decide +kernel
private theorem positive174_valid :
    check compatible fixed 2048 positive174 (actors174.filter (compatible 44))
      (allMasks.filter (fixed 44)) = true := by decide +kernel
theorem tree174_valid : check compatible fixed 2048 tree174 actors174 allMasks = true := by
  rw [tree174, check, negative174_valid, tree175_valid, Bool.true_and]
  exact positive174_valid
private theorem negative173_valid :
    actors173.filter (fun w => w != (175 : Fin 192)) = actors174 := by decide +kernel
private theorem positive173_valid :
    check compatible fixed 2048 positive173 (actors173.filter (compatible 175))
      (allMasks.filter (fixed 175)) = true := by decide +kernel
theorem tree173_valid : check compatible fixed 2048 tree173 actors173 allMasks = true := by
  rw [tree173, check, negative173_valid, tree174_valid, Bool.true_and]
  exact positive173_valid
private theorem negative172_valid :
    actors172.filter (fun w => w != (174 : Fin 192)) = actors173 := by decide +kernel
private theorem positive172_valid :
    check compatible fixed 2048 positive172 (actors172.filter (compatible 174))
      (allMasks.filter (fixed 174)) = true := by decide +kernel
theorem tree172_valid : check compatible fixed 2048 tree172 actors172 allMasks = true := by
  rw [tree172, check, negative172_valid, tree173_valid, Bool.true_and]
  exact positive172_valid
private theorem negative171_valid :
    actors171.filter (fun w => w != (173 : Fin 192)) = actors172 := by decide +kernel
private theorem positive171_valid :
    check compatible fixed 2048 positive171 (actors171.filter (compatible 173))
      (allMasks.filter (fixed 173)) = true := by decide +kernel
theorem tree171_valid : check compatible fixed 2048 tree171 actors171 allMasks = true := by
  rw [tree171, check, negative171_valid, tree172_valid, Bool.true_and]
  exact positive171_valid
private theorem negative170_valid :
    actors170.filter (fun w => w != (65 : Fin 192)) = actors171 := by decide +kernel
private theorem positive170_valid :
    check compatible fixed 2048 positive170 (actors170.filter (compatible 65))
      (allMasks.filter (fixed 65)) = true := by decide +kernel
theorem tree170_valid : check compatible fixed 2048 tree170 actors170 allMasks = true := by
  rw [tree170, check, negative170_valid, tree171_valid, Bool.true_and]
  exact positive170_valid
private theorem negative169_valid :
    actors169.filter (fun w => w != (172 : Fin 192)) = actors170 := by decide +kernel
private theorem positive169_valid :
    check compatible fixed 2048 positive169 (actors169.filter (compatible 172))
      (allMasks.filter (fixed 172)) = true := by decide +kernel
theorem tree169_valid : check compatible fixed 2048 tree169 actors169 allMasks = true := by
  rw [tree169, check, negative169_valid, tree170_valid, Bool.true_and]
  exact positive169_valid
private theorem negative168_valid :
    actors168.filter (fun w => w != (64 : Fin 192)) = actors169 := by decide +kernel
private theorem positive168_valid :
    check compatible fixed 2048 positive168 (actors168.filter (compatible 64))
      (allMasks.filter (fixed 64)) = true := by decide +kernel
theorem tree168_valid : check compatible fixed 2048 tree168 actors168 allMasks = true := by
  rw [tree168, check, negative168_valid, tree169_valid, Bool.true_and]
  exact positive168_valid
end Janko4.TwoRank.Finite
