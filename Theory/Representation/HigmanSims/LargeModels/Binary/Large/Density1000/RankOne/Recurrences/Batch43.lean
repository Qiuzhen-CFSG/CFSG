module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 688 through 703.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs43 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨688 + j.val, by omega⟩)

private theorem checked43 : dTree.checkProducts pairs43 = true := by
  decide +kernel

theorem step_product_43 (j : Fin 16) :
    dTree.product krylovRows[688 + j.val]! = krylovRows[688 + j.val + 1]! := by
  apply dTree.checked_product pairs43 checked43
  simp only [pairs43]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
