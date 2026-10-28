module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck04

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative151_valid :
    actors151.filter (fun w => w != (52 : Fin 192)) = actors152 := by decide +kernel
private theorem positive151_valid :
    check compatible fixed 2048 positive151 (actors151.filter (compatible 52))
      (allMasks.filter (fixed 52)) = true := by decide +kernel
theorem tree151_valid : check compatible fixed 2048 tree151 actors151 allMasks = true := by
  rw [tree151, check, negative151_valid, tree152_valid, Bool.true_and]
  exact positive151_valid
private theorem negative150_valid :
    actors150.filter (fun w => w != (113 : Fin 192)) = actors151 := by decide +kernel
private theorem positive150_valid :
    check compatible fixed 2048 positive150 (actors150.filter (compatible 113))
      (allMasks.filter (fixed 113)) = true := by decide +kernel
theorem tree150_valid : check compatible fixed 2048 tree150 actors150 allMasks = true := by
  rw [tree150, check, negative150_valid, tree151_valid, Bool.true_and]
  exact positive150_valid
private theorem negative149_valid :
    actors149.filter (fun w => w != (6 : Fin 192)) = actors150 := by decide +kernel
private theorem positive149_valid :
    check compatible fixed 2048 positive149 (actors149.filter (compatible 6))
      (allMasks.filter (fixed 6)) = true := by decide +kernel
theorem tree149_valid : check compatible fixed 2048 tree149 actors149 allMasks = true := by
  rw [tree149, check, negative149_valid, tree150_valid, Bool.true_and]
  exact positive149_valid
private theorem negative148_valid :
    actors148.filter (fun w => w != (130 : Fin 192)) = actors149 := by decide +kernel
private theorem positive148_valid :
    check compatible fixed 2048 positive148 (actors148.filter (compatible 130))
      (allMasks.filter (fixed 130)) = true := by decide +kernel
theorem tree148_valid : check compatible fixed 2048 tree148 actors148 allMasks = true := by
  rw [tree148, check, negative148_valid, tree149_valid, Bool.true_and]
  exact positive148_valid
private theorem negative147_valid :
    actors147.filter (fun w => w != (124 : Fin 192)) = actors148 := by decide +kernel
private theorem positive147_valid :
    check compatible fixed 2048 positive147 (actors147.filter (compatible 124))
      (allMasks.filter (fixed 124)) = true := by decide +kernel
theorem tree147_valid : check compatible fixed 2048 tree147 actors147 allMasks = true := by
  rw [tree147, check, negative147_valid, tree148_valid, Bool.true_and]
  exact positive147_valid
private theorem negative146_valid :
    actors146.filter (fun w => w != (3 : Fin 192)) = actors147 := by decide +kernel
private theorem positive146_valid :
    check compatible fixed 2048 positive146 (actors146.filter (compatible 3))
      (allMasks.filter (fixed 3)) = true := by decide +kernel
theorem tree146_valid : check compatible fixed 2048 tree146 actors146 allMasks = true := by
  rw [tree146, check, negative146_valid, tree147_valid, Bool.true_and]
  exact positive146_valid
private theorem negative145_valid :
    actors145.filter (fun w => w != (189 : Fin 192)) = actors146 := by decide +kernel
private theorem positive145_valid :
    check compatible fixed 2048 positive145 (actors145.filter (compatible 189))
      (allMasks.filter (fixed 189)) = true := by decide +kernel
theorem tree145_valid : check compatible fixed 2048 tree145 actors145 allMasks = true := by
  rw [tree145, check, negative145_valid, tree146_valid, Bool.true_and]
  exact positive145_valid
private theorem negative144_valid :
    actors144.filter (fun w => w != (186 : Fin 192)) = actors145 := by decide +kernel
private theorem positive144_valid :
    check compatible fixed 2048 positive144 (actors144.filter (compatible 186))
      (allMasks.filter (fixed 186)) = true := by decide +kernel
theorem tree144_valid : check compatible fixed 2048 tree144 actors144 allMasks = true := by
  rw [tree144, check, negative144_valid, tree145_valid, Bool.true_and]
  exact positive144_valid
end Janko4.TwoRank.Finite
