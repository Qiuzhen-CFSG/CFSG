module

public import Theory.SpecificGroups.Rudvalis.Model.PrimitiveData
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Kernel checks of the Rudvalis spanning forests

The forest edges give paths from 0 for the full action and paths from 0, 1,
and 6 for two explicit elements fixing 0. Every numerical assertion is checked
by kernel reduction against the ATLAS tables. No group-order computation is used.
See `PrimitiveData` for the data source and generation procedure.
-/

namespace Rudvalis.PrimitiveData

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

public theorem sMap_eq (x : Fin 4060) : sMap x = s • x := by
  revert x
  apply Data.allFin
  decide +kernel

public theorem tMap_eq (x : Fin 4060) : tMap x = t • x := by
  revert x
  apply Data.allFin
  decide +kernel

public theorem s_fix : s • (0 : Fin 4060) = 0 := by
  rw [← sMap_eq]
  decide +kernel

public theorem t_fix : t • (0 : Fin 4060) = 0 := by
  rw [← tMap_eq]
  decide +kernel

public theorem trans_edge (x : Fin 4060) : x = 0 ∨
    (transDepth (transParent x) < transDepth x ∧
      (Data.aMap (transParent x) = x ∨ Data.bMap (transParent x) = x)) := by
  revert x
  apply Data.allFin
  decide +kernel

public theorem stab_edge (x : Fin 4060) : x = root x ∨
    (stabDepth (stabParent x) < stabDepth x ∧ root (stabParent x) = root x ∧
      (sMap (stabParent x) = x ∨ tMap (stabParent x) = x)) := by
  revert x
  apply Data.allFin
  decide +kernel

public theorem root_cases (x : Fin 4060) : root x = 0 ∨ root x = 1 ∨ root x = 6 := by
  revert x
  apply Data.allFin
  decide +kernel

public theorem root_zero (x : Fin 4060) : root x = 0 ↔ x = 0 := by
  revert x
  apply Data.allFin
  decide +kernel

private def countNat (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => countNat f n + f n

private theorem countNat_eq (f : Nat → Nat) (n : Nat) :
    countNat f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [countNat]
  | succ n ih => simp only [countNat, Finset.sum_range_succ, ih]

private theorem ncard_setOf (P : Fin 4060 → Prop) [DecidablePred P] :
    {x | P x}.ncard = countNat
      (fun k => if P ⟨k % 4060, Nat.mod_lt _ (by decide)⟩ then 1 else 0) 4060 := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter, countNat_eq,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.mod_eq_of_lt i.isLt, Fin.eta]

public theorem first_union_card :
    {x : Fin 4060 | root x = 0 ∨ root x = 1}.ncard = 1756 := by
  rw [ncard_setOf]
  decide +kernel

public theorem second_union_card :
    {x : Fin 4060 | root x = 0 ∨ root x = 6}.ncard = 2305 := by
  rw [ncard_setOf]
  decide +kernel

end Rudvalis.PrimitiveData
