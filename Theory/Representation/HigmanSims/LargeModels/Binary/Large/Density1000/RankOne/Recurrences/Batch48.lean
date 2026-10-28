module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 768 through 783.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs48 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨768 + j.val, by omega⟩)

private theorem checked48 : dTree.checkProducts pairs48 = true := by
  decide +kernel

theorem step_product_48 (j : Fin 16) :
    dTree.product krylovRows[768 + j.val]! = krylovRows[768 + j.val + 1]! := by
  apply dTree.checked_product pairs48 checked48
  simp only [pairs48]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
