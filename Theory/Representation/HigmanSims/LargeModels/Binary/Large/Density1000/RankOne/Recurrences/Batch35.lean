module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 560 through 575.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs35 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨560 + j.val, by omega⟩)

private theorem checked35 : dTree.checkProducts pairs35 = true := by
  decide +kernel

theorem step_product_35 (j : Fin 16) :
    dTree.product krylovRows[560 + j.val]! = krylovRows[560 + j.val + 1]! := by
  apply dTree.checked_product pairs35 checked35
  simp only [pairs35]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
