module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 336 through 351.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs21 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨336 + j.val, by omega⟩)

private theorem checked21 : dTree.checkProducts pairs21 = true := by
  decide +kernel

theorem step_product_21 (j : Fin 16) :
    dTree.product krylovRows[336 + j.val]! = krylovRows[336 + j.val + 1]! := by
  apply dTree.checked_product pairs21 checked21
  simp only [pairs21]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
