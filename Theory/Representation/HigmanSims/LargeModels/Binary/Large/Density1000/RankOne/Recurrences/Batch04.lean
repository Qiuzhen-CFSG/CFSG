module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 64 through 79.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs04 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨64 + j.val, by omega⟩)

private theorem checked04 : dTree.checkProducts pairs04 = true := by
  decide +kernel

theorem step_product_04 (j : Fin 16) :
    dTree.product krylovRows[64 + j.val]! = krylovRows[64 + j.val + 1]! := by
  apply dTree.checked_product pairs04 checked04
  simp only [pairs04]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
