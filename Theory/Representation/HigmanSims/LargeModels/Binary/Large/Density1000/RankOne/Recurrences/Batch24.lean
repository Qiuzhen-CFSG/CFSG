module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 384 through 399.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs24 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨384 + j.val, by omega⟩)

private theorem checked24 : dTree.checkProducts pairs24 = true := by
  decide +kernel

theorem step_product_24 (j : Fin 16) :
    dTree.product krylovRows[384 + j.val]! = krylovRows[384 + j.val + 1]! := by
  apply dTree.checked_product pairs24 checked24
  simp only [pairs24]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
