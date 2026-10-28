module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck20

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative023_valid :
    actors023.filter (fun w => w != (179 : Fin 192)) = actors024 := by decide +kernel
private theorem positive023_valid :
    check compatible fixed 2048 positive023 (actors023.filter (compatible 179))
      (allMasks.filter (fixed 179)) = true := by decide +kernel
theorem tree023_valid : check compatible fixed 2048 tree023 actors023 allMasks = true := by
  rw [tree023, check, negative023_valid, tree024_valid, Bool.true_and]
  exact positive023_valid
private theorem negative022_valid :
    actors022.filter (fun w => w != (178 : Fin 192)) = actors023 := by decide +kernel
private theorem positive022_valid :
    check compatible fixed 2048 positive022 (actors022.filter (compatible 178))
      (allMasks.filter (fixed 178)) = true := by decide +kernel
theorem tree022_valid : check compatible fixed 2048 tree022 actors022 allMasks = true := by
  rw [tree022, check, negative022_valid, tree023_valid, Bool.true_and]
  exact positive022_valid
private theorem negative021_valid :
    actors021.filter (fun w => w != (177 : Fin 192)) = actors022 := by decide +kernel
private theorem positive021_valid :
    check compatible fixed 2048 positive021 (actors021.filter (compatible 177))
      (allMasks.filter (fixed 177)) = true := by decide +kernel
theorem tree021_valid : check compatible fixed 2048 tree021 actors021 allMasks = true := by
  rw [tree021, check, negative021_valid, tree022_valid, Bool.true_and]
  exact positive021_valid
private theorem negative020_valid :
    actors020.filter (fun w => w != (170 : Fin 192)) = actors021 := by decide +kernel
private theorem positive020_valid :
    check compatible fixed 2048 positive020 (actors020.filter (compatible 170))
      (allMasks.filter (fixed 170)) = true := by decide +kernel
theorem tree020_valid : check compatible fixed 2048 tree020 actors020 allMasks = true := by
  rw [tree020, check, negative020_valid, tree021_valid, Bool.true_and]
  exact positive020_valid
private theorem negative019_valid :
    actors019.filter (fun w => w != (43 : Fin 192)) = actors020 := by decide +kernel
private theorem positive019_valid :
    check compatible fixed 2048 positive019 (actors019.filter (compatible 43))
      (allMasks.filter (fixed 43)) = true := by decide +kernel
theorem tree019_valid : check compatible fixed 2048 tree019 actors019 allMasks = true := by
  rw [tree019, check, negative019_valid, tree020_valid, Bool.true_and]
  exact positive019_valid
private theorem negative018_valid :
    actors018.filter (fun w => w != (41 : Fin 192)) = actors019 := by decide +kernel
private theorem positive018_valid :
    check compatible fixed 2048 positive018 (actors018.filter (compatible 41))
      (allMasks.filter (fixed 41)) = true := by decide +kernel
theorem tree018_valid : check compatible fixed 2048 tree018 actors018 allMasks = true := by
  rw [tree018, check, negative018_valid, tree019_valid, Bool.true_and]
  exact positive018_valid
private theorem negative017_valid :
    actors017.filter (fun w => w != (88 : Fin 192)) = actors018 := by decide +kernel
private theorem positive017_valid :
    check compatible fixed 2048 positive017 (actors017.filter (compatible 88))
      (allMasks.filter (fixed 88)) = true := by decide +kernel
theorem tree017_valid : check compatible fixed 2048 tree017 actors017 allMasks = true := by
  rw [tree017, check, negative017_valid, tree018_valid, Bool.true_and]
  exact positive017_valid
private theorem negative016_valid :
    actors016.filter (fun w => w != (86 : Fin 192)) = actors017 := by decide +kernel
private theorem positive016_valid :
    check compatible fixed 2048 positive016 (actors016.filter (compatible 86))
      (allMasks.filter (fixed 86)) = true := by decide +kernel
theorem tree016_valid : check compatible fixed 2048 tree016 actors016 allMasks = true := by
  rw [tree016, check, negative016_valid, tree017_valid, Bool.true_and]
  exact positive016_valid
end Janko4.TwoRank.Finite
