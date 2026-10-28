module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks15
import Mathlib.Tactic.FinCases

/-! The sixteen bounded certificates cover the unchanged normal form exactly.
The count calculation reuses their small flag table, without repeating any
permutation calculation. Source: `FiniteData` and its checked ATLAS blocks. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFourTable_correct (n : Fin 1024) :
    hasOrderFour n = orderFourTable n := by
  have h (b : Fin 16) (k : Fin 64) :
      hasOrderFour (blockIndex b k) = orderFourTable (blockIndex b k) := by
    fin_cases b
    · exact orderFour_block_00 k
    · exact orderFour_block_01 k
    · exact orderFour_block_02 k
    · exact orderFour_block_03 k
    · exact orderFour_block_04 k
    · exact orderFour_block_05 k
    · exact orderFour_block_06 k
    · exact orderFour_block_07 k
    · exact orderFour_block_08 k
    · exact orderFour_block_09 k
    · exact orderFour_block_10 k
    · exact orderFour_block_11 k
    · exact orderFour_block_12 k
    · exact orderFour_block_13 k
    · exact orderFour_block_14 k
    · exact orderFour_block_15 k
  let b : Fin 16 := ⟨n.val / 64, by omega⟩
  let k : Fin 64 := ⟨n.val % 64, by omega⟩
  have hn : blockIndex b k = n := by
    apply Fin.ext
    dsimp [blockIndex, b, k]
    omega
  exact hn ▸ h b k

public theorem countTable_correct : ∀ v : Fin 16,
    ((List.finRange 1024).filter (fun n =>
      indexCode n == v.val && orderFourTable n)).length = countTable v.val := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
