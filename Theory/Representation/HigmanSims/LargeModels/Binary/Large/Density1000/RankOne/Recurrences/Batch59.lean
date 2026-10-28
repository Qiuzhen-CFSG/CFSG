module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 944 through 959.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs59 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨944 + j.val, by omega⟩)

private theorem checked59 : dTree.checkProducts pairs59 = true := by
  decide +kernel

theorem step_product_59 (j : Fin 16) :
    dTree.product krylovRows[944 + j.val]! = krylovRows[944 + j.val + 1]! := by
  apply dTree.checked_product pairs59 checked59
  simp only [pairs59]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
