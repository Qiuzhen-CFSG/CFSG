module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 416 through 431.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs26 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨416 + j.val, by omega⟩)

private theorem checked26 : dTree.checkProducts pairs26 = true := by
  decide +kernel

theorem step_product_26 (j : Fin 16) :
    dTree.product krylovRows[416 + j.val]! = krylovRows[416 + j.val + 1]! := by
  apply dTree.checked_product pairs26 checked26
  simp only [pairs26]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
