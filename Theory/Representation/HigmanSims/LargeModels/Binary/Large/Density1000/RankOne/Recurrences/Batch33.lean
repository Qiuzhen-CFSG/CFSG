module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 528 through 543.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs33 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨528 + j.val, by omega⟩)

private theorem checked33 : dTree.checkProducts pairs33 = true := by
  decide +kernel

theorem step_product_33 (j : Fin 16) :
    dTree.product krylovRows[528 + j.val]! = krylovRows[528 + j.val + 1]! := by
  apply dTree.checked_product pairs33 checked33
  simp only [pairs33]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
