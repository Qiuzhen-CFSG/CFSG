module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 432 through 447.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs27 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨432 + j.val, by omega⟩)

private theorem checked27 : dTree.checkProducts pairs27 = true := by
  decide +kernel

theorem step_product_27 (j : Fin 16) :
    dTree.product krylovRows[432 + j.val]! = krylovRows[432 + j.val + 1]! := by
  apply dTree.checked_product pairs27 checked27
  simp only [pairs27]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
