module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 192 through 207.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs12 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨192 + j.val, by omega⟩)

private theorem checked12 : dTree.checkProducts pairs12 = true := by
  decide +kernel

theorem step_product_12 (j : Fin 16) :
    dTree.product krylovRows[192 + j.val]! = krylovRows[192 + j.val + 1]! := by
  apply dTree.checked_product pairs12 checked12
  simp only [pairs12]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
