module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 832 through 847.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs52 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨832 + j.val, by omega⟩)

private theorem checked52 : dTree.checkProducts pairs52 = true := by
  decide +kernel

theorem step_product_52 (j : Fin 16) :
    dTree.product krylovRows[832 + j.val]! = krylovRows[832 + j.val + 1]! := by
  apply dTree.checked_product pairs52 checked52
  simp only [pairs52]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
