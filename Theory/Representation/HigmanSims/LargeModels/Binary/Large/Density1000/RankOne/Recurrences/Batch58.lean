module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 928 through 943.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs58 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨928 + j.val, by omega⟩)

private theorem checked58 : dTree.checkProducts pairs58 = true := by
  decide +kernel

theorem step_product_58 (j : Fin 16) :
    dTree.product krylovRows[928 + j.val]! = krylovRows[928 + j.val + 1]! := by
  apply dTree.checked_product pairs58 checked58
  simp only [pairs58]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
