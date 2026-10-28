module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 272 through 287.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs17 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨272 + j.val, by omega⟩)

private theorem checked17 : dTree.checkProducts pairs17 = true := by
  decide +kernel

theorem step_product_17 (j : Fin 16) :
    dTree.product krylovRows[272 + j.val]! = krylovRows[272 + j.val + 1]! := by
  apply dTree.checked_product pairs17 checked17
  simp only [pairs17]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
