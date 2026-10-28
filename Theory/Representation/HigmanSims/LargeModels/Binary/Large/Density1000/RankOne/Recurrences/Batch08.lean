module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 128 through 143.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs08 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨128 + j.val, by omega⟩)

private theorem checked08 : dTree.checkProducts pairs08 = true := by
  decide +kernel

theorem step_product_08 (j : Fin 16) :
    dTree.product krylovRows[128 + j.val]! = krylovRows[128 + j.val + 1]! := by
  apply dTree.checked_product pairs08 checked08
  simp only [pairs08]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
