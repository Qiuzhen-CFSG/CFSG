module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 32 through 47.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs02 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨32 + j.val, by omega⟩)

private theorem checked02 : dTree.checkProducts pairs02 = true := by
  decide +kernel

theorem step_product_02 (j : Fin 16) :
    dTree.product krylovRows[32 + j.val]! = krylovRows[32 + j.val + 1]! := by
  apply dTree.checked_product pairs02 checked02
  simp only [pairs02]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
