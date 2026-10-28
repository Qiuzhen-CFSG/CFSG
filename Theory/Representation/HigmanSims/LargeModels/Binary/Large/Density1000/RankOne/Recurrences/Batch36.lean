module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 576 through 591.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs36 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨576 + j.val, by omega⟩)

private theorem checked36 : dTree.checkProducts pairs36 = true := by
  decide +kernel

theorem step_product_36 (j : Fin 16) :
    dTree.product krylovRows[576 + j.val]! = krylovRows[576 + j.val + 1]! := by
  apply dTree.checked_product pairs36 checked36
  simp only [pairs36]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
