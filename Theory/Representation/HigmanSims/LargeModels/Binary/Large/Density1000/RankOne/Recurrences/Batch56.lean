module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 896 through 911.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs56 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨896 + j.val, by omega⟩)

private theorem checked56 : dTree.checkProducts pairs56 = true := by
  decide +kernel

theorem step_product_56 (j : Fin 16) :
    dTree.product krylovRows[896 + j.val]! = krylovRows[896 + j.val + 1]! := by
  apply dTree.checked_product pairs56 checked56
  simp only [pairs56]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
