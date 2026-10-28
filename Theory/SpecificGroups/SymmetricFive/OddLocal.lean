module

public import Theory.GroupTheory.CyclicFifteen
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Odd subgroups and five-cycle centralizers in S₅

An odd subgroup has order dividing fifteen. A group of order fifteen is
cyclic, while every permutation on five letters has order dividing twelve
or five, so the possible subgroup orders are one, three and five.
The centralizer of a five-cycle consists exactly of its powers, since
its support is the whole five-point set.

These elementary calculations supply the quotient steps in Aschbacher–Smith,
J.2.7(5), printed pp.435–436 (PDF pp.446–447 of `refs/quasithin.pdf`).
-/

public section
open Subgroup
namespace SymmetricFive

private theorem powers_symmetric_five : ∀ g : Equiv.Perm (Fin 5),
    g ^ 12 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

theorem odd_subgroup_card (A : Subgroup (Equiv.Perm (Fin 5)))
    (hodd : Odd (Nat.card A)) :
    Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 5 := by
  have hd : Nat.card A ∣ 2 ^ 3 * 15 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using
      A.card_subgroup_dvd_card
  have hd15 : Nat.card A ∣ 15 :=
    (Nat.coprime_two_left.mpr hodd).symm.pow_right 3 |>.dvd_of_dvd_mul_left hd
  have hcases : Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 5 ∨ Nat.card A = 15 := by
    have := Nat.mem_divisors.mpr ⟨hd15, (by decide : 15 ≠ 0)⟩
    have hdivs : Nat.divisors 15 = {1, 3, 5, 15} := by decide
    simpa only [hdivs, Finset.mem_insert, Finset.mem_singleton] using this
  rcases hcases with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · let : IsCyclic A := isCyclic_of_card_eq_fifteen h
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic A)
    have ho : orderOf (g : Equiv.Perm (Fin 5)) = 15 := (Subgroup.orderOf_coe g).trans (hg.trans h)
    rcases powers_symmetric_five g with hp | hp <;>
      have hd := orderOf_dvd_of_pow_eq_one hp <;> norm_num [ho] at hd

theorem centralizer_of_order_five {b : Equiv.Perm (Fin 5)} (hb : orderOf b = 5) :
    centralizer ({b} : Set (Equiv.Perm (Fin 5))) = zpowers b := by
  have hc : b.IsCycle := Equiv.Perm.isCycle_of_prime_order'' (by decide) hb
  have hs : b.support = Finset.univ := Finset.eq_univ_of_card _ (hc.orderOf.symm.trans hb)
  apply le_antisymm
  · intro g hg
    obtain ⟨hi, hm⟩ := hc.commute_iff.mp (mem_centralizer_singleton_iff.mp hg)
    have he : Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm g hi) = g := by
      apply Equiv.ext
      intro x
      exact Equiv.Perm.ofSubtype_subtypePerm_of_mem hi (hs ▸ Finset.mem_univ x)
    rwa [he] at hm
  · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

end SymmetricFive
