module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 608 through 623.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs38 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨608 + j.val, by omega⟩)

private theorem checked38 : dTree.checkProducts pairs38 = true := by
  decide +kernel

theorem step_product_38 (j : Fin 16) :
    dTree.product krylovRows[608 + j.val]! = krylovRows[608 + j.val + 1]! := by
  apply dTree.checked_product pairs38 checked38
  simp only [pairs38]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
