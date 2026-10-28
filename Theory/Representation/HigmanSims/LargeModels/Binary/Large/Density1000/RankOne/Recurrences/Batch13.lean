module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 208 through 223.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs13 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨208 + j.val, by omega⟩)

private theorem checked13 : dTree.checkProducts pairs13 = true := by
  decide +kernel

theorem step_product_13 (j : Fin 16) :
    dTree.product krylovRows[208 + j.val]! = krylovRows[208 + j.val + 1]! := by
  apply dTree.checked_product pairs13 checked13
  simp only [pairs13]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
