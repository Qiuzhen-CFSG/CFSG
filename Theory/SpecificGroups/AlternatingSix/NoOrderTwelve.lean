module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic

/-!
# Six-point permutations have no element of order twelve

An order-twelve permutation has cycle lengths dividing twelve. Under a
six-point bound, the only available lengths are two, three, four and six;
no multiset of those lengths with sum at most six has least common
multiple twelve. This supplies the D24 exclusion in the odd central
covers of A6 used in Aschbacher--Smith F.6.18(6), printed p.310.
-/

public section
namespace AlternatingSix
open Equiv
private def smallTypes : Finset (Multiset ℕ) :=
  {0, {2}, {3}, {4}, {6}, {2, 2}, {2, 3}, {2, 4}, {3, 3}, {2, 2, 2}}
private theorem small_types (m : Multiset ℕ) (hs : m.sum ≤ 6)
    (hm : ∀ n ∈ m, 2 ≤ n ∧ n ∣ 12) : m ∈ smallTypes := by
  induction m using Multiset.induction_on with
  | empty => decide
  | @cons a m ih =>
    have ha := hm a (by simp)
    have hb : a + m.sum ≤ 6 := by simpa using hs
    have h := ih (by omega) (fun n hn => hm n (by simp [hn]))
    have ha' : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 6 := by
      have ha6 : a ≤ 6 := by omega
      interval_cases a <;> norm_num at *
    simp only [smallTypes, Finset.mem_insert, Finset.mem_singleton] at h
    rcases ha' with rfl | rfl | rfl | rfl <;>
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hb
    all_goals decide +kernel

theorem perm_orderOf_ne_twelve (g : Perm (Fin 6)) : orderOf g ≠ 12 := by
  intro ho
  have hs := small_types g.cycleType (by simpa using g.sum_cycleType_le)
    (fun n hn => ⟨Perm.two_le_of_mem_cycleType hn, ho ▸ Perm.dvd_of_mem_cycleType hn⟩)
  have hl : g.cycleType.lcm = 12 := g.lcm_cycleType.trans ho
  simp only [smallTypes, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs <;>
    simp only [hs] at hl <;> norm_num [lcm_eq_nat_lcm] at hl

theorem orderOf_ne_twelve (g : alternatingGroup (Fin 6)) : orderOf g ≠ 12 := by
  simpa only [Subgroup.orderOf_coe] using perm_orderOf_ne_twelve (g : Perm (Fin 6))

end AlternatingSix
