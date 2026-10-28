module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 320 through 335.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs20 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨320 + j.val, by omega⟩)

private theorem checked20 : dTree.checkProducts pairs20 = true := by
  decide +kernel

theorem step_product_20 (j : Fin 16) :
    dTree.product krylovRows[320 + j.val]! = krylovRows[320 + j.val + 1]! := by
  apply dTree.checked_product pairs20 checked20
  simp only [pairs20]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
