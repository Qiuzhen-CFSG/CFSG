module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 960 through 975.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs60 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨960 + j.val, by omega⟩)

private theorem checked60 : dTree.checkProducts pairs60 = true := by
  decide +kernel

theorem step_product_60 (j : Fin 16) :
    dTree.product krylovRows[960 + j.val]! = krylovRows[960 + j.val + 1]! := by
  apply dTree.checked_product pairs60 checked60
  simp only [pairs60]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
