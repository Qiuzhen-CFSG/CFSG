module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 16 through 31.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs01 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨16 + j.val, by omega⟩)

private theorem checked01 : dTree.checkProducts pairs01 = true := by
  decide +kernel

theorem step_product_01 (j : Fin 16) :
    dTree.product krylovRows[16 + j.val]! = krylovRows[16 + j.val + 1]! := by
  apply dTree.checked_product pairs01 checked01
  simp only [pairs01]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
