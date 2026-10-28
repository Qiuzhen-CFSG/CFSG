module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck16

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative055_valid :
    actors055.filter (fun w => w != (191 : Fin 192)) = actors056 := by decide +kernel
private theorem positive055_valid :
    check compatible fixed 2048 positive055 (actors055.filter (compatible 191))
      (allMasks.filter (fixed 191)) = true := by decide +kernel
theorem tree055_valid : check compatible fixed 2048 tree055 actors055 allMasks = true := by
  rw [tree055, check, negative055_valid, tree056_valid, Bool.true_and]
  exact positive055_valid
private theorem negative054_valid :
    actors054.filter (fun w => w != (76 : Fin 192)) = actors055 := by decide +kernel
private theorem positive054_valid :
    check compatible fixed 2048 positive054 (actors054.filter (compatible 76))
      (allMasks.filter (fixed 76)) = true := by decide +kernel
theorem tree054_valid : check compatible fixed 2048 tree054 actors054 allMasks = true := by
  rw [tree054, check, negative054_valid, tree055_valid, Bool.true_and]
  exact positive054_valid
private theorem negative053_valid :
    actors053.filter (fun w => w != (160 : Fin 192)) = actors054 := by decide +kernel
private theorem positive053_valid :
    check compatible fixed 2048 positive053 (actors053.filter (compatible 160))
      (allMasks.filter (fixed 160)) = true := by decide +kernel
theorem tree053_valid : check compatible fixed 2048 tree053 actors053 allMasks = true := by
  rw [tree053, check, negative053_valid, tree054_valid, Bool.true_and]
  exact positive053_valid
private theorem negative052_valid :
    actors052.filter (fun w => w != (69 : Fin 192)) = actors053 := by decide +kernel
private theorem positive052_valid :
    check compatible fixed 2048 positive052 (actors052.filter (compatible 69))
      (allMasks.filter (fixed 69)) = true := by decide +kernel
theorem tree052_valid : check compatible fixed 2048 tree052 actors052 allMasks = true := by
  rw [tree052, check, negative052_valid, tree053_valid, Bool.true_and]
  exact positive052_valid
private theorem negative051_valid :
    actors051.filter (fun w => w != (149 : Fin 192)) = actors052 := by decide +kernel
private theorem positive051_valid :
    check compatible fixed 2048 positive051 (actors051.filter (compatible 149))
      (allMasks.filter (fixed 149)) = true := by decide +kernel
theorem tree051_valid : check compatible fixed 2048 tree051 actors051 allMasks = true := by
  rw [tree051, check, negative051_valid, tree052_valid, Bool.true_and]
  exact positive051_valid
private theorem negative050_valid :
    actors050.filter (fun w => w != (148 : Fin 192)) = actors051 := by decide +kernel
private theorem positive050_valid :
    check compatible fixed 2048 positive050 (actors050.filter (compatible 148))
      (allMasks.filter (fixed 148)) = true := by decide +kernel
theorem tree050_valid : check compatible fixed 2048 tree050 actors050 allMasks = true := by
  rw [tree050, check, negative050_valid, tree051_valid, Bool.true_and]
  exact positive050_valid
private theorem negative049_valid :
    actors049.filter (fun w => w != (145 : Fin 192)) = actors050 := by decide +kernel
private theorem positive049_valid :
    check compatible fixed 2048 positive049 (actors049.filter (compatible 145))
      (allMasks.filter (fixed 145)) = true := by decide +kernel
theorem tree049_valid : check compatible fixed 2048 tree049 actors049 allMasks = true := by
  rw [tree049, check, negative049_valid, tree050_valid, Bool.true_and]
  exact positive049_valid
private theorem negative048_valid :
    actors048.filter (fun w => w != (128 : Fin 192)) = actors049 := by decide +kernel
private theorem positive048_valid :
    check compatible fixed 2048 positive048 (actors048.filter (compatible 128))
      (allMasks.filter (fixed 128)) = true := by decide +kernel
theorem tree048_valid : check compatible fixed 2048 tree048 actors048 allMasks = true := by
  rw [tree048, check, negative048_valid, tree049_valid, Bool.true_and]
  exact positive048_valid
end Janko4.TwoRank.Finite
