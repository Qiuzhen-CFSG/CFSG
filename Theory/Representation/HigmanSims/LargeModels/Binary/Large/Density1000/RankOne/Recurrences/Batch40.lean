module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences.Base

/-! Bounded kernel check for recurrence transitions 640 through 655.

The list has 16 adjacent rows, so its reduction stays within the measured
bounded-check boundary. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

private def pairs40 : List (ℕ × ℕ) :=
  (List.finRange 16).map (fun j => stepPair ⟨640 + j.val, by omega⟩)

private theorem checked40 : dTree.checkProducts pairs40 = true := by
  decide +kernel

theorem step_product_40 (j : Fin 16) :
    dTree.product krylovRows[640 + j.val]! = krylovRows[640 + j.val + 1]! := by
  apply dTree.checked_product pairs40 checked40
  simp only [pairs40]
  apply List.mem_map.mpr
  exact ⟨j, List.mem_finRange j, rfl⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
