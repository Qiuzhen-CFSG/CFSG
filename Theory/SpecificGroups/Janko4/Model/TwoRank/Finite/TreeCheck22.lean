module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck21

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative015_valid :
    actors015.filter (fun w => w != (51 : Fin 192)) = actors016 := by decide +kernel
private theorem positive015_valid :
    check compatible fixed 2048 positive015 (actors015.filter (compatible 51))
      (allMasks.filter (fixed 51)) = true := by decide +kernel
theorem tree015_valid : check compatible fixed 2048 tree015 actors015 allMasks = true := by
  rw [tree015, check, negative015_valid, tree016_valid, Bool.true_and]
  exact positive015_valid
private theorem negative014_valid :
    actors014.filter (fun w => w != (49 : Fin 192)) = actors015 := by decide +kernel
private theorem positive014_valid :
    check compatible fixed 2048 positive014 (actors014.filter (compatible 49))
      (allMasks.filter (fixed 49)) = true := by decide +kernel
theorem tree014_valid : check compatible fixed 2048 tree014 actors014 allMasks = true := by
  rw [tree014, check, negative014_valid, tree015_valid, Bool.true_and]
  exact positive014_valid
private theorem negative013_valid :
    actors013.filter (fun w => w != (48 : Fin 192)) = actors014 := by decide +kernel
private theorem positive013_valid :
    check compatible fixed 2048 positive013 (actors013.filter (compatible 48))
      (allMasks.filter (fixed 48)) = true := by decide +kernel
theorem tree013_valid : check compatible fixed 2048 tree013 actors013 allMasks = true := by
  rw [tree013, check, negative013_valid, tree014_valid, Bool.true_and]
  exact positive013_valid
private theorem negative012_valid :
    actors012.filter (fun w => w != (120 : Fin 192)) = actors013 := by decide +kernel
private theorem positive012_valid :
    check compatible fixed 2048 positive012 (actors012.filter (compatible 120))
      (allMasks.filter (fixed 120)) = true := by decide +kernel
theorem tree012_valid : check compatible fixed 2048 tree012 actors012 allMasks = true := by
  rw [tree012, check, negative012_valid, tree013_valid, Bool.true_and]
  exact positive012_valid
private theorem negative011_valid :
    actors011.filter (fun w => w != (103 : Fin 192)) = actors012 := by decide +kernel
private theorem positive011_valid :
    check compatible fixed 2048 positive011 (actors011.filter (compatible 103))
      (allMasks.filter (fixed 103)) = true := by decide +kernel
theorem tree011_valid : check compatible fixed 2048 tree011 actors011 allMasks = true := by
  rw [tree011, check, negative011_valid, tree012_valid, Bool.true_and]
  exact positive011_valid
private theorem negative010_valid :
    actors010.filter (fun w => w != (102 : Fin 192)) = actors011 := by decide +kernel
private theorem positive010_valid :
    check compatible fixed 2048 positive010 (actors010.filter (compatible 102))
      (allMasks.filter (fixed 102)) = true := by decide +kernel
theorem tree010_valid : check compatible fixed 2048 tree010 actors010 allMasks = true := by
  rw [tree010, check, negative010_valid, tree011_valid, Bool.true_and]
  exact positive010_valid
private theorem negative009_valid :
    actors009.filter (fun w => w != (100 : Fin 192)) = actors010 := by decide +kernel
private theorem positive009_valid :
    check compatible fixed 2048 positive009 (actors009.filter (compatible 100))
      (allMasks.filter (fixed 100)) = true := by decide +kernel
theorem tree009_valid : check compatible fixed 2048 tree009 actors009 allMasks = true := by
  rw [tree009, check, negative009_valid, tree010_valid, Bool.true_and]
  exact positive009_valid
private theorem negative008_valid :
    actors008.filter (fun w => w != (14 : Fin 192)) = actors009 := by decide +kernel
private theorem positive008_valid :
    check compatible fixed 2048 positive008 (actors008.filter (compatible 14))
      (allMasks.filter (fixed 14)) = true := by decide +kernel
theorem tree008_valid : check compatible fixed 2048 tree008 actors008 allMasks = true := by
  rw [tree008, check, negative008_valid, tree009_valid, Bool.true_and]
  exact positive008_valid
end Janko4.TwoRank.Finite
