module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 480 through 495.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs30 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨480 + j.val, by omega⟩)

private theorem checked30 : dTree.checkProducts pairs30 = true := by
  decide +kernel

theorem step_product_30 (j : Fin 16) :
    dTree.product krylovRows[480 + j.val]! = krylovRows[480 + j.val + 1]! := by
  apply dTree.checked_product pairs30 checked30
  simp only [pairs30]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
