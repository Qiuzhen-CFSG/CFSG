module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck09

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative111_valid :
    actors111.filter (fun w => w != (13 : Fin 192)) = actors112 := by decide +kernel
private theorem positive111_valid :
    check compatible fixed 2048 positive111 (actors111.filter (compatible 13))
      (allMasks.filter (fixed 13)) = true := by decide +kernel
theorem tree111_valid : check compatible fixed 2048 tree111 actors111 allMasks = true := by
  rw [tree111, check, negative111_valid, tree112_valid, Bool.true_and]
  exact positive111_valid
private theorem negative110_valid :
    actors110.filter (fun w => w != (12 : Fin 192)) = actors111 := by decide +kernel
private theorem positive110_valid :
    check compatible fixed 2048 positive110 (actors110.filter (compatible 12))
      (allMasks.filter (fixed 12)) = true := by decide +kernel
theorem tree110_valid : check compatible fixed 2048 tree110 actors110 allMasks = true := by
  rw [tree110, check, negative110_valid, tree111_valid, Bool.true_and]
  exact positive110_valid
private theorem negative109_valid :
    actors109.filter (fun w => w != (90 : Fin 192)) = actors110 := by decide +kernel
private theorem positive109_valid :
    check compatible fixed 2048 positive109 (actors109.filter (compatible 90))
      (allMasks.filter (fixed 90)) = true := by decide +kernel
theorem tree109_valid : check compatible fixed 2048 tree109 actors109 allMasks = true := by
  rw [tree109, check, negative109_valid, tree110_valid, Bool.true_and]
  exact positive109_valid
private theorem negative108_valid :
    actors108.filter (fun w => w != (8 : Fin 192)) = actors109 := by decide +kernel
private theorem positive108_valid :
    check compatible fixed 2048 positive108 (actors108.filter (compatible 8))
      (allMasks.filter (fixed 8)) = true := by decide +kernel
theorem tree108_valid : check compatible fixed 2048 tree108 actors108 allMasks = true := by
  rw [tree108, check, negative108_valid, tree109_valid, Bool.true_and]
  exact positive108_valid
private theorem negative107_valid :
    actors107.filter (fun w => w != (87 : Fin 192)) = actors108 := by decide +kernel
private theorem positive107_valid :
    check compatible fixed 2048 positive107 (actors107.filter (compatible 87))
      (allMasks.filter (fixed 87)) = true := by decide +kernel
theorem tree107_valid : check compatible fixed 2048 tree107 actors107 allMasks = true := by
  rw [tree107, check, negative107_valid, tree108_valid, Bool.true_and]
  exact positive107_valid
private theorem negative106_valid :
    actors106.filter (fun w => w != (50 : Fin 192)) = actors107 := by decide +kernel
private theorem positive106_valid :
    check compatible fixed 2048 positive106 (actors106.filter (compatible 50))
      (allMasks.filter (fixed 50)) = true := by decide +kernel
theorem tree106_valid : check compatible fixed 2048 tree106 actors106 allMasks = true := by
  rw [tree106, check, negative106_valid, tree107_valid, Bool.true_and]
  exact positive106_valid
private theorem negative105_valid :
    actors105.filter (fun w => w != (84 : Fin 192)) = actors106 := by decide +kernel
private theorem positive105_valid :
    check compatible fixed 2048 positive105 (actors105.filter (compatible 84))
      (allMasks.filter (fixed 84)) = true := by decide +kernel
theorem tree105_valid : check compatible fixed 2048 tree105 actors105 allMasks = true := by
  rw [tree105, check, negative105_valid, tree106_valid, Bool.true_and]
  exact positive105_valid
private theorem negative104_valid :
    actors104.filter (fun w => w != (1 : Fin 192)) = actors105 := by decide +kernel
private theorem positive104_valid :
    check compatible fixed 2048 positive104 (actors104.filter (compatible 1))
      (allMasks.filter (fixed 1)) = true := by decide +kernel
theorem tree104_valid : check compatible fixed 2048 tree104 actors104 allMasks = true := by
  rw [tree104, check, negative104_valid, tree105_valid, Bool.true_and]
  exact positive104_valid
end Janko4.TwoRank.Finite
