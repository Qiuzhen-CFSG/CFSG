module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 96 through 111.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs06 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨96 + j.val, by omega⟩)

private theorem checked06 : dTree.checkProducts pairs06 = true := by
  decide +kernel

theorem step_product_06 (j : Fin 16) :
    dTree.product krylovRows[96 + j.val]! = krylovRows[96 + j.val + 1]! := by
  apply dTree.checked_product pairs06 checked06
  simp only [pairs06]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
