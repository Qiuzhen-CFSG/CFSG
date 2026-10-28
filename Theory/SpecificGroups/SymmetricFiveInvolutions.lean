module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Outer involutions of the symmetric group on five letters

An odd permutation of order two has exactly one two-cycle: two disjoint
two-cycles would be even, and three require six letters. The cycle-count
formula gives ten such transpositions, without enumerating permutations.

Application: the H/Q calculation in Aschbacher–Smith, J.2.6, printed p.435.
-/

public section
namespace Equiv.Perm

/-- Every odd involution on five letters is a transposition. -/
theorem five_isSwap_of_outer_involution (t : Perm (Fin 5))
    (ht : orderOf t = 2) (hout : t ∉ alternatingGroup (Fin 5)) : t.IsSwap := by
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (σ := t) (ht ▸ Nat.prime_two)
  rw [ht] at hk
  have hb := t.sum_cycleType_le
  rw [hk, Multiset.sum_replicate] at hb
  simp only [smul_eq_mul, Fintype.card_fin] at hb
  have hk1 : k ≤ 1 := by omega
  interval_cases k
  · exact Equiv.Perm.isSwap_iff_cycleType.mpr (by simpa using hk)
  · apply False.elim
    apply hout
    rw [Equiv.Perm.mem_alternatingGroup]
    rw [Equiv.Perm.sign_of_cycleType, hk]
    norm_num
    decide

/-- There are ten transpositions on five letters. -/
theorem card_five_transpositions : Nat.card {t : Perm (Fin 5) // t.IsSwap} = 10 := by
  classical
  have he : {t : Perm (Fin 5) | t.IsSwap} = {t : Perm (Fin 5) | t.cycleType = {2}} := by
    ext t
    exact Equiv.Perm.isSwap_iff_cycleType
  rw [show Nat.card {t : Perm (Fin 5) // t.IsSwap} = Nat.card ({t : Perm (Fin 5) | t.IsSwap}) from rfl, he,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Set.mem_ofPred_eq]
  rw [Equiv.Perm.card_of_cycleType_singleton (by decide) (by decide)]
  norm_num [Nat.choose]

end Equiv.Perm
