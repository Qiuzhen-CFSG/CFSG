module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 784 through 799.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs49 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨784 + j.val, by omega⟩)

private theorem checked49 : dTree.checkProducts pairs49 = true := by
  decide +kernel

theorem step_product_49 (j : Fin 16) :
    dTree.product krylovRows[784 + j.val]! = krylovRows[784 + j.val + 1]! := by
  apply dTree.checked_product pairs49 checked49
  simp only [pairs49]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
