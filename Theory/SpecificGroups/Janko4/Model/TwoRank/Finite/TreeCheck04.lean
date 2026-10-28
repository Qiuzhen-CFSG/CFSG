module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck03

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative159_valid :
    actors159.filter (fun w => w != (15 : Fin 192)) = actors160 := by decide +kernel
private theorem positive159_valid :
    check compatible fixed 2048 positive159 (actors159.filter (compatible 15))
      (allMasks.filter (fixed 15)) = true := by decide +kernel
theorem tree159_valid : check compatible fixed 2048 tree159 actors159 allMasks = true := by
  rw [tree159, check, negative159_valid, tree160_valid, Bool.true_and]
  exact positive159_valid
private theorem negative158_valid :
    actors158.filter (fun w => w != (34 : Fin 192)) = actors159 := by decide +kernel
private theorem positive158_valid :
    check compatible fixed 2048 positive158 (actors158.filter (compatible 34))
      (allMasks.filter (fixed 34)) = true := by decide +kernel
theorem tree158_valid : check compatible fixed 2048 tree158 actors158 allMasks = true := by
  rw [tree158, check, negative158_valid, tree159_valid, Bool.true_and]
  exact positive158_valid
private theorem negative157_valid :
    actors157.filter (fun w => w != (33 : Fin 192)) = actors158 := by decide +kernel
private theorem positive157_valid :
    check compatible fixed 2048 positive157 (actors157.filter (compatible 33))
      (allMasks.filter (fixed 33)) = true := by decide +kernel
theorem tree157_valid : check compatible fixed 2048 tree157 actors157 allMasks = true := by
  rw [tree157, check, negative157_valid, tree158_valid, Bool.true_and]
  exact positive157_valid
private theorem negative156_valid :
    actors156.filter (fun w => w != (78 : Fin 192)) = actors157 := by decide +kernel
private theorem positive156_valid :
    check compatible fixed 2048 positive156 (actors156.filter (compatible 78))
      (allMasks.filter (fixed 78)) = true := by decide +kernel
theorem tree156_valid : check compatible fixed 2048 tree156 actors156 allMasks = true := by
  rw [tree156, check, negative156_valid, tree157_valid, Bool.true_and]
  exact positive156_valid
private theorem negative155_valid :
    actors155.filter (fun w => w != (140 : Fin 192)) = actors156 := by decide +kernel
private theorem positive155_valid :
    check compatible fixed 2048 positive155 (actors155.filter (compatible 140))
      (allMasks.filter (fixed 140)) = true := by decide +kernel
theorem tree155_valid : check compatible fixed 2048 tree155 actors155 allMasks = true := by
  rw [tree155, check, negative155_valid, tree156_valid, Bool.true_and]
  exact positive155_valid
private theorem negative154_valid :
    actors154.filter (fun w => w != (32 : Fin 192)) = actors155 := by decide +kernel
private theorem positive154_valid :
    check compatible fixed 2048 positive154 (actors154.filter (compatible 32))
      (allMasks.filter (fixed 32)) = true := by decide +kernel
theorem tree154_valid : check compatible fixed 2048 tree154 actors154 allMasks = true := by
  rw [tree154, check, negative154_valid, tree155_valid, Bool.true_and]
  exact positive154_valid
private theorem negative153_valid :
    actors153.filter (fun w => w != (139 : Fin 192)) = actors154 := by decide +kernel
private theorem positive153_valid :
    check compatible fixed 2048 positive153 (actors153.filter (compatible 139))
      (allMasks.filter (fixed 139)) = true := by decide +kernel
theorem tree153_valid : check compatible fixed 2048 tree153 actors153 allMasks = true := by
  rw [tree153, check, negative153_valid, tree154_valid, Bool.true_and]
  exact positive153_valid
private theorem negative152_valid :
    actors152.filter (fun w => w != (115 : Fin 192)) = actors153 := by decide +kernel
private theorem positive152_valid :
    check compatible fixed 2048 positive152 (actors152.filter (compatible 115))
      (allMasks.filter (fixed 115)) = true := by decide +kernel
theorem tree152_valid : check compatible fixed 2048 tree152 actors152 allMasks = true := by
  rw [tree152, check, negative152_valid, tree153_valid, Bool.true_and]
  exact positive152_valid
end Janko4.TwoRank.Finite
