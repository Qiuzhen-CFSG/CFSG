module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 592 through 607.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs37 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨592 + j.val, by omega⟩)

private theorem checked37 : dTree.checkProducts pairs37 = true := by
  decide +kernel

theorem step_product_37 (j : Fin 16) :
    dTree.product krylovRows[592 + j.val]! = krylovRows[592 + j.val + 1]! := by
  apply dTree.checked_product pairs37 checked37
  simp only [pairs37]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
