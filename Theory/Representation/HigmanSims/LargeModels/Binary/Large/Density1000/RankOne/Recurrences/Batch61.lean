module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 976 through 991.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs61 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨976 + j.val, by omega⟩)

private theorem checked61 : dTree.checkProducts pairs61 = true := by
  decide +kernel

theorem step_product_61 (j : Fin 16) :
    dTree.product krylovRows[976 + j.val]! = krylovRows[976 + j.val + 1]! := by
  apply dTree.checked_product pairs61 checked61
  simp only [pairs61]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
