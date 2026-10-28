module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 352 through 367.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs22 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨352 + j.val, by omega⟩)

private theorem checked22 : dTree.checkProducts pairs22 = true := by
  decide +kernel

theorem step_product_22 (j : Fin 16) :
    dTree.product krylovRows[352 + j.val]! = krylovRows[352 + j.val + 1]! := by
  apply dTree.checked_product pairs22 checked22
  simp only [pairs22]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
