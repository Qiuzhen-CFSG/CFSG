module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 48 through 63.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs03 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨48 + j.val, by omega⟩)

private theorem checked03 : dTree.checkProducts pairs03 = true := by
  decide +kernel

theorem step_product_03 (j : Fin 16) :
    dTree.product krylovRows[48 + j.val]! = krylovRows[48 + j.val + 1]! := by
  apply dTree.checked_product pairs03 checked03
  simp only [pairs03]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
