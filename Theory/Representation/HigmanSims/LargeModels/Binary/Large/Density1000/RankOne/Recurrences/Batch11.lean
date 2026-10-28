module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 176 through 191.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs11 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨176 + j.val, by omega⟩)

private theorem checked11 : dTree.checkProducts pairs11 = true := by
  decide +kernel

theorem step_product_11 (j : Fin 16) :
    dTree.product krylovRows[176 + j.val]! = krylovRows[176 + j.val + 1]! := by
  apply dTree.checked_product pairs11 checked11
  simp only [pairs11]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
