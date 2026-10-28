module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 992 through 998.

The list has 7 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs62 : List (ℕ × ℕ) :=
  (List.finRange 7).map (fun j => stepPair ⟨992 + j.val, by omega⟩)

private theorem checked62 : dTree.checkProducts pairs62 = true := by
  decide +kernel

theorem step_product_62 (j : Fin 7) :
    dTree.product krylovRows[992 + j.val]! = krylovRows[992 + j.val + 1]! := by
  apply dTree.checked_product pairs62 checked62
  simp only [pairs62]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
