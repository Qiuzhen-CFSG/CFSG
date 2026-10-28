module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 496 through 511.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs31 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨496 + j.val, by omega⟩)

private theorem checked31 : dTree.checkProducts pairs31 = true := by
  decide +kernel

theorem step_product_31 (j : Fin 16) :
    dTree.product krylovRows[496 + j.val]! = krylovRows[496 + j.val + 1]! := by
  apply dTree.checked_product pairs31 checked31
  simp only [pairs31]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
