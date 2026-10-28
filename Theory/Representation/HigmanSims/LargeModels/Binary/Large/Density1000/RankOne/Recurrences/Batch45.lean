module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 720 through 735.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs45 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨720 + j.val, by omega⟩)

private theorem checked45 : dTree.checkProducts pairs45 = true := by
  decide +kernel

theorem step_product_45 (j : Fin 16) :
    dTree.product krylovRows[720 + j.val]! = krylovRows[720 + j.val + 1]! := by
  apply dTree.checked_product pairs45 checked45
  simp only [pairs45]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
