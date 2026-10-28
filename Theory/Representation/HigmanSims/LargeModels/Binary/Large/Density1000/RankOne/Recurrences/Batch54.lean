module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 864 through 879.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs54 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨864 + j.val, by omega⟩)

private theorem checked54 : dTree.checkProducts pairs54 = true := by
  decide +kernel

theorem step_product_54 (j : Fin 16) :
    dTree.product krylovRows[864 + j.val]! = krylovRows[864 + j.val + 1]! := by
  apply dTree.checked_product pairs54 checked54
  simp only [pairs54]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
