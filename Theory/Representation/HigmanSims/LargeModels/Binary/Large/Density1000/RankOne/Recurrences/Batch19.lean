module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 304 through 319.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs19 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨304 + j.val, by omega⟩)

private theorem checked19 : dTree.checkProducts pairs19 = true := by
  decide +kernel

theorem step_product_19 (j : Fin 16) :
    dTree.product krylovRows[304 + j.val]! = krylovRows[304 + j.val + 1]! := by
  apply dTree.checked_product pairs19 checked19
  simp only [pairs19]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
