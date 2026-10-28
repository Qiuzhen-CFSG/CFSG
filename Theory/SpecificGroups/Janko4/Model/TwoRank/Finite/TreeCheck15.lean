module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.TreeCheck14

/-! Checked branching certificates, evaluated separately to bound kernel memory. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open Theory.GroupAction.BinaryCliqueFixedBound
private theorem negative071_valid :
    actors071.filter (fun w => w != (138 : Fin 192)) = actors072 := by decide +kernel
private theorem positive071_valid :
    check compatible fixed 2048 positive071 (actors071.filter (compatible 138))
      (allMasks.filter (fixed 138)) = true := by decide +kernel
theorem tree071_valid : check compatible fixed 2048 tree071 actors071 allMasks = true := by
  rw [tree071, check, negative071_valid, tree072_valid, Bool.true_and]
  exact positive071_valid
private theorem negative070_valid :
    actors070.filter (fun w => w != (134 : Fin 192)) = actors071 := by decide +kernel
private theorem positive070_valid :
    check compatible fixed 2048 positive070 (actors070.filter (compatible 134))
      (allMasks.filter (fixed 134)) = true := by decide +kernel
theorem tree070_valid : check compatible fixed 2048 tree070 actors070 allMasks = true := by
  rw [tree070, check, negative070_valid, tree071_valid, Bool.true_and]
  exact positive070_valid
private theorem negative069_valid :
    actors069.filter (fun w => w != (131 : Fin 192)) = actors070 := by decide +kernel
private theorem positive069_valid :
    check compatible fixed 2048 positive069 (actors069.filter (compatible 131))
      (allMasks.filter (fixed 131)) = true := by decide +kernel
theorem tree069_valid : check compatible fixed 2048 tree069 actors069 allMasks = true := by
  rw [tree069, check, negative069_valid, tree070_valid, Bool.true_and]
  exact positive069_valid
private theorem negative068_valid :
    actors068.filter (fun w => w != (129 : Fin 192)) = actors069 := by decide +kernel
private theorem positive068_valid :
    check compatible fixed 2048 positive068 (actors068.filter (compatible 129))
      (allMasks.filter (fixed 129)) = true := by decide +kernel
theorem tree068_valid : check compatible fixed 2048 tree068 actors068 allMasks = true := by
  rw [tree068, check, negative068_valid, tree069_valid, Bool.true_and]
  exact positive068_valid
private theorem negative067_valid :
    actors067.filter (fun w => w != (185 : Fin 192)) = actors068 := by decide +kernel
private theorem positive067_valid :
    check compatible fixed 2048 positive067 (actors067.filter (compatible 185))
      (allMasks.filter (fixed 185)) = true := by decide +kernel
theorem tree067_valid : check compatible fixed 2048 tree067 actors067 allMasks = true := by
  rw [tree067, check, negative067_valid, tree068_valid, Bool.true_and]
  exact positive067_valid
private theorem negative066_valid :
    actors066.filter (fun w => w != (184 : Fin 192)) = actors067 := by decide +kernel
private theorem positive066_valid :
    check compatible fixed 2048 positive066 (actors066.filter (compatible 184))
      (allMasks.filter (fixed 184)) = true := by decide +kernel
theorem tree066_valid : check compatible fixed 2048 tree066 actors066 allMasks = true := by
  rw [tree066, check, negative066_valid, tree067_valid, Bool.true_and]
  exact positive066_valid
private theorem negative065_valid :
    actors065.filter (fun w => w != (181 : Fin 192)) = actors066 := by decide +kernel
private theorem positive065_valid :
    check compatible fixed 2048 positive065 (actors065.filter (compatible 181))
      (allMasks.filter (fixed 181)) = true := by decide +kernel
theorem tree065_valid : check compatible fixed 2048 tree065 actors065 allMasks = true := by
  rw [tree065, check, negative065_valid, tree066_valid, Bool.true_and]
  exact positive065_valid
private theorem negative064_valid :
    actors064.filter (fun w => w != (180 : Fin 192)) = actors065 := by decide +kernel
private theorem positive064_valid :
    check compatible fixed 2048 positive064 (actors064.filter (compatible 180))
      (allMasks.filter (fixed 180)) = true := by decide +kernel
theorem tree064_valid : check compatible fixed 2048 tree064 actors064 allMasks = true := by
  rw [tree064, check, negative064_valid, tree065_valid, Bool.true_and]
  exact positive064_valid
end Janko4.TwoRank.Finite
