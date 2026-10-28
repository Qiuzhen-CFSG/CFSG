module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 112 through 127.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs07 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨112 + j.val, by omega⟩)

private theorem checked07 : dTree.checkProducts pairs07 = true := by
  decide +kernel

theorem step_product_07 (j : Fin 16) :
    dTree.product krylovRows[112 + j.val]! = krylovRows[112 + j.val + 1]! := by
  apply dTree.checked_product pairs07 checked07
  simp only [pairs07]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
