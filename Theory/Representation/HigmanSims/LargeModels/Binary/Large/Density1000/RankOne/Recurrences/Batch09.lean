module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 144 through 159.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs09 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨144 + j.val, by omega⟩)

private theorem checked09 : dTree.checkProducts pairs09 = true := by
  decide +kernel

theorem step_product_09 (j : Fin 16) :
    dTree.product krylovRows[144 + j.val]! = krylovRows[144 + j.val + 1]! := by
  apply dTree.checked_product pairs09 checked09
  simp only [pairs09]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
