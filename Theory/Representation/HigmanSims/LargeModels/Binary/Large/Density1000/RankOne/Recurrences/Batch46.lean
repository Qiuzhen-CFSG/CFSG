module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 736 through 751.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs46 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨736 + j.val, by omega⟩)

private theorem checked46 : dTree.checkProducts pairs46 = true := by
  decide +kernel

theorem step_product_46 (j : Fin 16) :
    dTree.product krylovRows[736 + j.val]! = krylovRows[736 + j.val + 1]! := by
  apply dTree.checked_product pairs46 checked46
  simp only [pairs46]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
