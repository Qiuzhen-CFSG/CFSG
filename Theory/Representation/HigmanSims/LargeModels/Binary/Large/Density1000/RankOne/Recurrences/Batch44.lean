module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 704 through 719.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs44 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨704 + j.val, by omega⟩)

private theorem checked44 : dTree.checkProducts pairs44 = true := by
  decide +kernel

theorem step_product_44 (j : Fin 16) :
    dTree.product krylovRows[704 + j.val]! = krylovRows[704 + j.val + 1]! := by
  apply dTree.checked_product pairs44 checked44
  simp only [pairs44]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
