module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 544 through 559.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs34 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨544 + j.val, by omega⟩)

private theorem checked34 : dTree.checkProducts pairs34 = true := by
  decide +kernel

theorem step_product_34 (j : Fin 16) :
    dTree.product krylovRows[544 + j.val]! = krylovRows[544 + j.val + 1]! := by
  apply dTree.checked_product pairs34 checked34
  simp only [pairs34]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
