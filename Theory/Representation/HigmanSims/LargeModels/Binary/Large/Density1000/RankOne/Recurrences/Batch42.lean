module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 672 through 687.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs42 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨672 + j.val, by omega⟩)

private theorem checked42 : dTree.checkProducts pairs42 = true := by
  decide +kernel

theorem step_product_42 (j : Fin 16) :
    dTree.product krylovRows[672 + j.val]! = krylovRows[672 + j.val + 1]! := by
  apply dTree.checked_product pairs42 checked42
  simp only [pairs42]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
