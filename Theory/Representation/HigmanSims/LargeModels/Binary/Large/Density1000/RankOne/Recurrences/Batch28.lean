module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 448 through 463.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs28 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨448 + j.val, by omega⟩)

private theorem checked28 : dTree.checkProducts pairs28 = true := by
  decide +kernel

theorem step_product_28 (j : Fin 16) :
    dTree.product krylovRows[448 + j.val]! = krylovRows[448 + j.val + 1]! := by
  apply dTree.checked_product pairs28 checked28
  simp only [pairs28]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
