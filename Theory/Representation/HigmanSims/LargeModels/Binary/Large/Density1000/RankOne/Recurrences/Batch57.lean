module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 912 through 927.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs57 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨912 + j.val, by omega⟩)

private theorem checked57 : dTree.checkProducts pairs57 = true := by
  decide +kernel

theorem step_product_57 (j : Fin 16) :
    dTree.product krylovRows[912 + j.val]! = krylovRows[912 + j.val + 1]! := by
  apply dTree.checked_product pairs57 checked57
  simp only [pairs57]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
