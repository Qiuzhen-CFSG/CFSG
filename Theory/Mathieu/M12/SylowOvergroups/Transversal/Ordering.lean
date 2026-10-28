module

public import Theory.Mathieu.M12.SylowOvergroups.Transversal.Data
public import Mathlib.Data.List.Chain

/-!
# Strict increase of the coset keys

A linear adjacent-pair check on the underlying list proves strict increase.
This avoids reducing a large universal quantifier over array indices.
-/

public section
namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups

set_option maxRecDepth 1000000

theorem keyTable_size : keyTable.size = 1485 := by decide +kernel

theorem keyTable_chain : keyTable.toList.IsChain (· < ·) := by decide +kernel

theorem keyTable_strictMono : StrictMono (fun j : Fin 1485 => keyTable[j.val]!) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hi : i.val + 1 < keyTable.toList.length := by
    rw [Array.length_toList, keyTable_size]
    exact i.succ.isLt
  have h := (List.isChain_iff_getElem.mp keyTable_chain) i.val hi
  have h0 : i.val < keyTable.size := by rw [keyTable_size]; omega
  have h1 : i.val + 1 < keyTable.size := by simpa using hi
  simpa only [Fin.val_castSucc, Fin.val_succ, Array.getElem_toList,
    getElem!_pos keyTable i.val h0, getElem!_pos keyTable (i.val + 1) h1] using h

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
