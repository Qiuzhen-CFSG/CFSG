module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 624 through 639.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs39 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨624 + j.val, by omega⟩)

private theorem checked39 : dTree.checkProducts pairs39 = true := by
  decide +kernel

theorem step_product_39 (j : Fin 16) :
    dTree.product krylovRows[624 + j.val]! = krylovRows[624 + j.val + 1]! := by
  apply dTree.checked_product pairs39 checked39
  simp only [pairs39]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
