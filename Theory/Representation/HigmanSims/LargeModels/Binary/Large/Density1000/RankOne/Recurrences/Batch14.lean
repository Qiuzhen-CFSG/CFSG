module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 224 through 239.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs14 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨224 + j.val, by omega⟩)

private theorem checked14 : dTree.checkProducts pairs14 = true := by
  decide +kernel

theorem step_product_14 (j : Fin 16) :
    dTree.product krylovRows[224 + j.val]! = krylovRows[224 + j.val + 1]! := by
  apply dTree.checked_product pairs14 checked14
  simp only [pairs14]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
