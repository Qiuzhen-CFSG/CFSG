module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 752 through 767.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs47 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨752 + j.val, by omega⟩)

private theorem checked47 : dTree.checkProducts pairs47 = true := by
  decide +kernel

theorem step_product_47 (j : Fin 16) :
    dTree.product krylovRows[752 + j.val]! = krylovRows[752 + j.val + 1]! := by
  apply dTree.checked_product pairs47 checked47
  simp only [pairs47]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
