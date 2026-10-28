module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck10

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative103_valid :
    actors103.filter (fun w => w != (71 : Fin 192)) = actors104 := by decide +kernel
private theorem positive103_valid :
    check compatible fixed 2048 positive103 (actors103.filter (compatible 71))
      (allMasks.filter (fixed 71)) = true := by decide +kernel
theorem tree103_valid : check compatible fixed 2048 tree103 actors103 allMasks = true := by
  rw [tree103, check, negative103_valid, tree104_valid, Bool.true_and]
  exact positive103_valid
private theorem negative102_valid :
    actors102.filter (fun w => w != (70 : Fin 192)) = actors103 := by decide +kernel
private theorem positive102_valid :
    check compatible fixed 2048 positive102 (actors102.filter (compatible 70))
      (allMasks.filter (fixed 70)) = true := by decide +kernel
theorem tree102_valid : check compatible fixed 2048 tree102 actors102 allMasks = true := by
  rw [tree102, check, negative102_valid, tree103_valid, Bool.true_and]
  exact positive102_valid
private theorem negative101_valid :
    actors101.filter (fun w => w != (63 : Fin 192)) = actors102 := by decide +kernel
private theorem positive101_valid :
    check compatible fixed 2048 positive101 (actors101.filter (compatible 63))
      (allMasks.filter (fixed 63)) = true := by decide +kernel
theorem tree101_valid : check compatible fixed 2048 tree101 actors101 allMasks = true := by
  rw [tree101, check, negative101_valid, tree102_valid, Bool.true_and]
  exact positive101_valid
private theorem negative100_valid :
    actors100.filter (fun w => w != (62 : Fin 192)) = actors101 := by decide +kernel
private theorem positive100_valid :
    check compatible fixed 2048 positive100 (actors100.filter (compatible 62))
      (allMasks.filter (fixed 62)) = true := by decide +kernel
theorem tree100_valid : check compatible fixed 2048 tree100 actors100 allMasks = true := by
  rw [tree100, check, negative100_valid, tree101_valid, Bool.true_and]
  exact positive100_valid
private theorem negative099_valid :
    actors099.filter (fun w => w != (58 : Fin 192)) = actors100 := by decide +kernel
private theorem positive099_valid :
    check compatible fixed 2048 positive099 (actors099.filter (compatible 58))
      (allMasks.filter (fixed 58)) = true := by decide +kernel
theorem tree099_valid : check compatible fixed 2048 tree099 actors099 allMasks = true := by
  rw [tree099, check, negative099_valid, tree100_valid, Bool.true_and]
  exact positive099_valid
private theorem negative098_valid :
    actors098.filter (fun w => w != (57 : Fin 192)) = actors099 := by decide +kernel
private theorem positive098_valid :
    check compatible fixed 2048 positive098 (actors098.filter (compatible 57))
      (allMasks.filter (fixed 57)) = true := by decide +kernel
theorem tree098_valid : check compatible fixed 2048 tree098 actors098 allMasks = true := by
  rw [tree098, check, negative098_valid, tree099_valid, Bool.true_and]
  exact positive098_valid
private theorem negative097_valid :
    actors097.filter (fun w => w != (56 : Fin 192)) = actors098 := by decide +kernel
private theorem positive097_valid :
    check compatible fixed 2048 positive097 (actors097.filter (compatible 56))
      (allMasks.filter (fixed 56)) = true := by decide +kernel
theorem tree097_valid : check compatible fixed 2048 tree097 actors097 allMasks = true := by
  rw [tree097, check, negative097_valid, tree098_valid, Bool.true_and]
  exact positive097_valid
private theorem negative096_valid :
    actors096.filter (fun w => w != (55 : Fin 192)) = actors097 := by decide +kernel
private theorem positive096_valid :
    check compatible fixed 2048 positive096 (actors096.filter (compatible 55))
      (allMasks.filter (fixed 55)) = true := by decide +kernel
theorem tree096_valid : check compatible fixed 2048 tree096 actors096 allMasks = true := by
  rw [tree096, check, negative096_valid, tree097_valid, Bool.true_and]
  exact positive096_valid
end Janko4.TwoRank.Finite
