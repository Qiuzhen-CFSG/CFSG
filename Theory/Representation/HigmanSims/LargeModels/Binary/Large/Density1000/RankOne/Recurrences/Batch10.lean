module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 160 through 175.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs10 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨160 + j.val, by omega⟩)

private theorem checked10 : dTree.checkProducts pairs10 = true := by
  decide +kernel

theorem step_product_10 (j : Fin 16) :
    dTree.product krylovRows[160 + j.val]! = krylovRows[160 + j.val + 1]! := by
  apply dTree.checked_product pairs10 checked10
  simp only [pairs10]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
