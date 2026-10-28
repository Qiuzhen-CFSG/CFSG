module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 288 through 303.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs18 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨288 + j.val, by omega⟩)

private theorem checked18 : dTree.checkProducts pairs18 = true := by
  decide +kernel

theorem step_product_18 (j : Fin 16) :
    dTree.product krylovRows[288 + j.val]! = krylovRows[288 + j.val + 1]! := by
  apply dTree.checked_product pairs18 checked18
  simp only [pairs18]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
