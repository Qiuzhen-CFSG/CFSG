module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 368 through 383.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs23 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨368 + j.val, by omega⟩)

private theorem checked23 : dTree.checkProducts pairs23 = true := by
  decide +kernel

theorem step_product_23 (j : Fin 16) :
    dTree.product krylovRows[368 + j.val]! = krylovRows[368 + j.val + 1]! := by
  apply dTree.checked_product pairs23 checked23
  simp only [pairs23]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
