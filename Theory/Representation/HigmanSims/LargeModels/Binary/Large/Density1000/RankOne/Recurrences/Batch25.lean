module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 400 through 415.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs25 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨400 + j.val, by omega⟩)

private theorem checked25 : dTree.checkProducts pairs25 = true := by
  decide +kernel

theorem step_product_25 (j : Fin 16) :
    dTree.product krylovRows[400 + j.val]! = krylovRows[400 + j.val + 1]! := by
  apply dTree.checked_product pairs25 checked25
  simp only [pairs25]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
