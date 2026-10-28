module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck06

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative135_valid :
    actors135.filter (fun w => w != (59 : Fin 192)) = actors136 := by decide +kernel
private theorem positive135_valid :
    check compatible fixed 2048 positive135 (actors135.filter (compatible 59))
      (allMasks.filter (fixed 59)) = true := by decide +kernel
theorem tree135_valid : check compatible fixed 2048 tree135 actors135 allMasks = true := by
  rw [tree135, check, negative135_valid, tree136_valid, Bool.true_and]
  exact positive135_valid
private theorem negative134_valid :
    actors134.filter (fun w => w != (18 : Fin 192)) = actors135 := by decide +kernel
private theorem positive134_valid :
    check compatible fixed 2048 positive134 (actors134.filter (compatible 18))
      (allMasks.filter (fixed 18)) = true := by decide +kernel
theorem tree134_valid : check compatible fixed 2048 tree134 actors134 allMasks = true := by
  rw [tree134, check, negative134_valid, tree135_valid, Bool.true_and]
  exact positive134_valid
private theorem negative133_valid :
    actors133.filter (fun w => w != (54 : Fin 192)) = actors134 := by decide +kernel
private theorem positive133_valid :
    check compatible fixed 2048 positive133 (actors133.filter (compatible 54))
      (allMasks.filter (fixed 54)) = true := by decide +kernel
theorem tree133_valid : check compatible fixed 2048 tree133 actors133 allMasks = true := by
  rw [tree133, check, negative133_valid, tree134_valid, Bool.true_and]
  exact positive133_valid
private theorem negative132_valid :
    actors132.filter (fun w => w != (75 : Fin 192)) = actors133 := by decide +kernel
private theorem positive132_valid :
    check compatible fixed 2048 positive132 (actors132.filter (compatible 75))
      (allMasks.filter (fixed 75)) = true := by decide +kernel
theorem tree132_valid : check compatible fixed 2048 tree132 actors132 allMasks = true := by
  rw [tree132, check, negative132_valid, tree133_valid, Bool.true_and]
  exact positive132_valid
private theorem negative131_valid :
    actors131.filter (fun w => w != (74 : Fin 192)) = actors132 := by decide +kernel
private theorem positive131_valid :
    check compatible fixed 2048 positive131 (actors131.filter (compatible 74))
      (allMasks.filter (fixed 74)) = true := by decide +kernel
theorem tree131_valid : check compatible fixed 2048 tree131 actors131 allMasks = true := by
  rw [tree131, check, negative131_valid, tree132_valid, Bool.true_and]
  exact positive131_valid
private theorem negative130_valid :
    actors130.filter (fun w => w != (73 : Fin 192)) = actors131 := by decide +kernel
private theorem positive130_valid :
    check compatible fixed 2048 positive130 (actors130.filter (compatible 73))
      (allMasks.filter (fixed 73)) = true := by decide +kernel
theorem tree130_valid : check compatible fixed 2048 tree130 actors130 allMasks = true := by
  rw [tree130, check, negative130_valid, tree131_valid, Bool.true_and]
  exact positive130_valid
private theorem negative129_valid :
    actors129.filter (fun w => w != (72 : Fin 192)) = actors130 := by decide +kernel
private theorem positive129_valid :
    check compatible fixed 2048 positive129 (actors129.filter (compatible 72))
      (allMasks.filter (fixed 72)) = true := by decide +kernel
theorem tree129_valid : check compatible fixed 2048 tree129 actors129 allMasks = true := by
  rw [tree129, check, negative129_valid, tree130_valid, Bool.true_and]
  exact positive129_valid
private theorem negative128_valid :
    actors128.filter (fun w => w != (133 : Fin 192)) = actors129 := by decide +kernel
private theorem positive128_valid :
    check compatible fixed 2048 positive128 (actors128.filter (compatible 133))
      (allMasks.filter (fixed 133)) = true := by decide +kernel
theorem tree128_valid : check compatible fixed 2048 tree128 actors128 allMasks = true := by
  rw [tree128, check, negative128_valid, tree129_valid, Bool.true_and]
  exact positive128_valid
end Janko4.TwoRank.Finite
