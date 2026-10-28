module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 512 through 527.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs32 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨512 + j.val, by omega⟩)

private theorem checked32 : dTree.checkProducts pairs32 = true := by
  decide +kernel

theorem step_product_32 (j : Fin 16) :
    dTree.product krylovRows[512 + j.val]! = krylovRows[512 + j.val + 1]! := by
  apply dTree.checked_product pairs32 checked32
  simp only [pairs32]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
