module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 816 through 831.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs51 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨816 + j.val, by omega⟩)

private theorem checked51 : dTree.checkProducts pairs51 = true := by
  decide +kernel

theorem step_product_51 (j : Fin 16) :
    dTree.product krylovRows[816 + j.val]! = krylovRows[816 + j.val + 1]! := by
  apply dTree.checked_product pairs51 checked51
  simp only [pairs51]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
