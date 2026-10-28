module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 848 through 863.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs53 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨848 + j.val, by omega⟩)

private theorem checked53 : dTree.checkProducts pairs53 = true := by
  decide +kernel

theorem step_product_53 (j : Fin 16) :
    dTree.product krylovRows[848 + j.val]! = krylovRows[848 + j.val + 1]! := by
  apply dTree.checked_product pairs53 checked53
  simp only [pairs53]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
