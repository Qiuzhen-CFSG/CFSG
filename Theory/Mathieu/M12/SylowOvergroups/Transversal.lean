module

public import Theory.Mathieu.M12.SylowOvergroups.Transversal.Block0
public import Theory.Mathieu.M12.SylowOvergroups.Transversal.Block1
public import Theory.Mathieu.M12.SylowOvergroups.Transversal.Block2
public import Theory.Mathieu.M12.SylowOvergroups.Transversal.Block3
public import Theory.Mathieu.M12.SylowOvergroups.Transversal.Block4
public import Theory.Mathieu.M12.SylowOvergroups.Transversal.Ordering

/-! The kernel checks the coset keys against their numerical table. Strict
increase of that table certifies that all 1,485 cosets are distinct. -/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups
set_option maxRecDepth 1000000

set_option maxHeartbeats 4000000 in
theorem transversalKey_eq : ∀ j : Fin 1485, transversalKey j = keyTable[j.val]! := by
  intro j
  let a : Fin 5 := ⟨j.val / 297, by omega⟩
  let b : Fin 297 := ⟨j.val % 297, Nat.mod_lt _ (by decide)⟩
  have hj : blockIndex a b = j := by
    apply Fin.ext
    dsimp [blockIndex, a, b]
    omega
  have h (x : Fin 5) : ∀ y : Fin 297,
      explicitKey (transversalPerm (blockIndex x y)) = keyTable[(blockIndex x y).val]! := by
    fin_cases x
    · exact key_block_0
    · exact key_block_1
    · exact key_block_2
    · exact key_block_3
    · exact key_block_4
  rw [transversalKey_explicit, ← hj]
  exact h a b

theorem transversalKey_injective : Function.Injective transversalKey := by
  have h : transversalKey = fun j : Fin 1485 => keyTable[j.val]! := funext transversalKey_eq
  rw [h]
  exact keyTable_strictMono.injective

theorem transversal_cosets_injective : Function.Injective
    (fun j : Fin 1485 => (QuotientGroup.mk (transversal j) : M12 ⧸ sylowCandidate)) := by
  intro i j h
  apply transversalKey_injective
  simpa only [cosetKey_transversal] using key_eq_of_coset_eq h

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
