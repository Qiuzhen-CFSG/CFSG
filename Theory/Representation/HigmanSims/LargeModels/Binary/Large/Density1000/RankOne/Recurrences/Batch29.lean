module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 464 through 479.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs29 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨464 + j.val, by omega⟩)

private theorem checked29 : dTree.checkProducts pairs29 = true := by
  decide +kernel

theorem step_product_29 (j : Fin 16) :
    dTree.product krylovRows[464 + j.val]! = krylovRows[464 + j.val + 1]! := by
  apply dTree.checked_product pairs29 checked29
  simp only [pairs29]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
