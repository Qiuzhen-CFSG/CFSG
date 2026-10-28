module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 0 through 15.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs00 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨j.val, by omega⟩)

private theorem checked00 : dTree.checkProducts pairs00 = true := by
  decide +kernel

theorem step_product_00 (j : Fin 16) :
    dTree.product krylovRows[j.val]! = krylovRows[j.val + 1]! := by
  apply dTree.checked_product pairs00 checked00
  simp only [pairs00]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
