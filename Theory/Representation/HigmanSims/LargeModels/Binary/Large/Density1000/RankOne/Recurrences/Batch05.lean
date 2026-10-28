module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 80 through 95.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs05 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨80 + j.val, by omega⟩)

private theorem checked05 : dTree.checkProducts pairs05 = true := by
  decide +kernel

theorem step_product_05 (j : Fin 16) :
    dTree.product krylovRows[80 + j.val]! = krylovRows[80 + j.val + 1]! := by
  apply dTree.checked_product pairs05 checked05
  simp only [pairs05]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
