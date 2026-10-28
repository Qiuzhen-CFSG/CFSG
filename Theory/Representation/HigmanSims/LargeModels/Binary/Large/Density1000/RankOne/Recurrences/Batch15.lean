module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 240 through 255.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs15 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨240 + j.val, by omega⟩)

private theorem checked15 : dTree.checkProducts pairs15 = true := by
  decide +kernel

theorem step_product_15 (j : Fin 16) :
    dTree.product krylovRows[240 + j.val]! = krylovRows[240 + j.val + 1]! := by
  apply dTree.checked_product pairs15 checked15
  simp only [pairs15]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
