module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

/-!
# Cubic generators for S₄ overgroups of a fixed dihedral Sylow in A₇

Fix the rotation (0123)(45) and reflection (01)(23). A cubic generator in
an S₄ overgroup satisfies (cr²)³ = (cr)⁴ = 1. Kernel-checked inspection of
all seven-point permutations shows that exactly four orbits under the
fixed eight-group occur. Mathlib's permutation-list theorem proves coverage;
the inspection is split into 42 blocks of 120 permutations.

Source: the local inspection in Aschbacher--Smith F.6.18, printed p.310.
The finite data is reproducible from the definitions; no classification or
external enumeration is a proof premise.
-/

@[expose] public section

open Equiv Subgroup
namespace AlternatingSeven.DihedralLocals
abbrev Perm7 := Perm (Fin 7)
abbrev A7 := alternatingGroup (Fin 7)
def r : Perm7 := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5
def s : Perm7 := swap 0 1 * swap 2 3
def tWord (i : Fin 8) : Perm7 := r ^ (i.val % 4) * s ^ (i.val / 4)
def cubic (j : Fin 4) : Perm7 :=
  match j.val with
  | 0 => swap 1 2 * swap 2 3
  | 1 => (swap 1 2 * swap 2 3) * (swap 4 5 * swap 5 6)
  | 2 => (swap 1 2 * swap 2 3) * (swap 4 6 * swap 6 5)
  | _ => (swap 0 1 * swap 1 4) * (swap 2 3 * swap 3 5)

def Criterion (a : Perm7) : Prop :=
  a ^ 3 = 1 ∧ a ≠ 1 ∧ (a * r ^ 2) ^ 3 = 1 ∧ (a * r) ^ 4 = 1
private def Conclusion (a : Perm7) : Prop := ∃ j : Fin 4, ∃ i : Fin 8, a = tWord i * cubic j * (tWord i)⁻¹
private instance (a : Perm7) : Decidable (Criterion a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private instance (a : Perm7) : Decidable (Conclusion a) := inferInstanceAs (Decidable (∃ _j : Fin 4, ∃ _i : Fin 8, _))
private def Block (i : Fin 7) (j : Fin 6) : Prop :=
  ∀ a ∈ permsOfList ([2,3,4,5,6] : List (Fin 7)),
    Criterion (swap 0 i * swap 1 j.succ * a) → Conclusion (swap 0 i * swap 1 j.succ * a)
private instance (i : Fin 7) (j : Fin 6) : Decidable (Block i j) := List.decidableBAll _ _
set_option maxRecDepth 10000 in
private theorem blocks (i : Fin 7) (j : Fin 6) : Block i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem split_perms {i : Fin 7} {l : List (Fin 7)} (a : Perm7)
    (ha : a ∈ permsOfList (i :: l)) :
    ∃ j ∈ i :: l, ∃ b ∈ permsOfList l, a = swap i j * b := by
  rw [permsOfList] at ha
  rcases List.mem_append.mp ha with h | h
  · exact ⟨i, by simp, a, h, by rw [swap_self]; rfl⟩
  · obtain ⟨j, hj, hj'⟩ := List.mem_flatMap.mp h
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp hj'
    exact ⟨j, List.mem_cons_of_mem _ hj, b, hb, hba.symm⟩

-- The first two swap choices give 7 · 6 blocks and cover every permutation;
-- this is proved from Mathlib's exhaustive permutation-list construction.
private theorem split_seven (a : Perm7) :
    ∃ i : Fin 7, ∃ j : Fin 6, ∃ b ∈ permsOfList ([2, 3, 4, 5, 6] : List (Fin 7)),
      a = swap 0 i * swap 1 j.succ * b := by
  have ha : a ∈ permsOfList ([0, 1, 2, 3, 4, 5, 6] : List (Fin 7)) :=
    mem_permsOfList_of_mem (by intro x _; fin_cases x <;> simp)
  obtain ⟨i, _, b, hb, hab⟩ := split_perms a ha
  obtain ⟨j, hj, c, hc, hbc⟩ := split_perms b hb
  have hj0 : j ≠ 0 := by intro h; subst j; simp at hj
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
  exact ⟨i, k, c, hc, by rw [hab, hbc, mul_assoc]⟩
/-- All cubic elements satisfying the literal S₄ identities are conjugates
of the four displayed representatives by the fixed eight-group. -/
theorem cubic_catalogue (a : Perm7) (ha : Criterion a) :
    ∃ j : Fin 4, ∃ i : Fin 8, a = tWord i * cubic j * (tWord i)⁻¹ := by
  obtain ⟨i, j, b, hb, rfl⟩ := split_seven a
  exact blocks i j b hb ha

end AlternatingSeven.DihedralLocals
