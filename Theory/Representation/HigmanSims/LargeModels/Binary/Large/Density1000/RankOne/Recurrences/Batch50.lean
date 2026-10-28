module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 800 through 815.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs50 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨800 + j.val, by omega⟩)

private theorem checked50 : dTree.checkProducts pairs50 = true := by
  decide +kernel

theorem step_product_50 (j : Fin 16) :
    dTree.product krylovRows[800 + j.val]! = krylovRows[800 + j.val + 1]! := by
  apply dTree.checked_product pairs50 checked50
  simp only [pairs50]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
