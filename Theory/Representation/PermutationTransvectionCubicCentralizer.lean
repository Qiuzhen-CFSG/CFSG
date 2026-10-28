module

public import Theory.Representation.SixLetterTransvections
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.Tactic

/-!
# Cubics centralizing six- and seven-letter transvections

The cycle type of an involution on six or seven letters has at most three
transpositions. A three-cycle on fixed letters centralizes a single
transposition, and also a double transposition on seven letters. Simultaneously
rotating the three swapped pairs centralizes a triple transposition. These
permutations are even, hence belong to the derived subgroup.

Only the double-transposition case on six letters lacks such a cubic. The
faithful binary displacement obstruction in `SixLetterTransvections` excludes
that case whenever the marked element moves at most one dimension. No choice
between a natural module and a permutation core is needed for this argument.

The representative identities below are small kernel-checked certificates;
all involutions are covered structurally by their cycle types and conjugacy.
Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
G.6.4, printed pp.345–346, and the split paragraph of 15.3.58, printed p.1149.
-/

public section

namespace Representation.PermutationTransvectionCubicCentralizer
open _root_.Equiv _root_.Equiv.Perm

private def rep (n k : ℕ) : Perm (Fin (n + 6)) :=
  ([swap 0 1, swap 2 3, swap 4 5].take k).prod

private theorem rep_cycleType (n : Fin 2) (k : Fin 4) :
    (rep n k).cycleType = Multiset.replicate k 2 := by
  fin_cases n <;> fin_cases k <;> decide +kernel

private def cubic (n : ℕ) (k : ℕ) : Perm (Fin (n + 6)) :=
  if k = 3 then swap 0 2 * swap 2 4 * (swap 1 3 * swap 3 5)
  else if k = 2 then swap 4 5 * swap 5 6
  else swap 2 3 * swap 3 4

private theorem certificate (n : Fin 2) (k : Fin 4)
    (hk : k = 1 ∨ k = 3 ∨ (n = 1 ∧ k = 2)) :
    (cubic n k).sign = 1 ∧
      (cubic n k) ^ 3 = 1 ∧ cubic n k ≠ 1 ∧
      Commute (cubic n k) (rep n k) := by
  fin_cases n <;> fin_cases k <;> revert hk <;>
    unfold Commute SemiconjBy <;> decide +kernel

/-- An actor isomorphism transports a derived-subgroup cubic centralizer witness. -/
theorem exists_commuting_cubic_map {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) {t : A}
    (h : ∃ c ∈ commutator A, orderOf c = 3 ∧ Commute c t) :
    ∃ c ∈ commutator B, orderOf c = 3 ∧ Commute c (e t) := by
  obtain ⟨c, hc, ho, ht⟩ := h
  refine ⟨e c, ?_, (e.orderOf_eq c).trans ho, ht.map e⟩
  have hm : (commutator A).map e.toMonoidHom ≤ commutator B := by
    rw [commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hm (Subgroup.mem_map_of_mem e.toMonoidHom hc)

private theorem rep_cubic (n : Fin 2) (k : Fin 4)
    (hk : k = 1 ∨ k = 3 ∨ (n = 1 ∧ k = 2)) :
    ∃ c ∈ commutator (Perm (Fin (n.val + 6))),
      orderOf c = 3 ∧ Commute c (rep n k) := by
  obtain ⟨hs, hp, hn, hc⟩ := certificate n k hk
  refine ⟨cubic n k, ?_, orderOf_eq_prime_iff.mpr ⟨hp, hn⟩, hc⟩
  rw [alternatingGroup.commutator_perm_eq (by simp)]
  exact hs

/-- Every odd involution of S₆ centralizes an element of order three in A₆. -/
theorem exists_commuting_cubic_six_of_odd_involution (t : Perm (Fin 6))
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) (hodd : t.sign ≠ 1) :
    ∃ c ∈ commutator (Perm (Fin 6)), orderOf c = 3 ∧ Commute c t := by
  have hc := cycleType_of_pow_prime_eq_one ht2
  have hn : t.cycleType.card ≤ 3 := by
    have hsum := t.sum_cycleType_le
    rw [hc, Multiset.sum_replicate] at hsum
    simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hsum
    omega
  have hpos := card_cycleType_pos.mpr ht
  have hnot : t.cycleType.card ≠ 2 := by
    intro he
    apply hodd
    rw [sign_of_cycleType', hc, he]
    decide +kernel
  have hrep : IsConj (rep 0 t.cycleType.card) t := by
    apply isConj_of_cycleType_eq
    exact (rep_cycleType 0 ⟨t.cycleType.card, by omega⟩).trans hc.symm
  have hh := rep_cubic 0 ⟨t.cycleType.card, by omega⟩ (by
    have hd : t.cycleType.card = 1 ∨ t.cycleType.card = 3 := by omega
    rcases hd with hd | hd
    · exact Or.inl (Fin.ext hd)
    · exact Or.inr (Or.inl (Fin.ext hd)))
  obtain ⟨g, hg⟩ := isConj_iff.mp hrep
  simpa only [Fin.val_zero, Fin.val_one, MulAut.conj_apply, hg] using
    exists_commuting_cubic_map (MulAut.conj g) hh

/-- Every nonidentity involution of S₇ centralizes an element of order three in A₇. -/
theorem exists_commuting_cubic_seven_of_involution (t : Perm (Fin 7))
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ c ∈ commutator (Perm (Fin 7)), orderOf c = 3 ∧ Commute c t := by
  have hc := cycleType_of_pow_prime_eq_one ht2
  have hn : t.cycleType.card ≤ 3 := by
    have hsum := t.sum_cycleType_le
    rw [hc, Multiset.sum_replicate] at hsum
    simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hsum
    omega
  have hpos := card_cycleType_pos.mpr ht
  have hrep : IsConj (rep 1 t.cycleType.card) t := by
    apply isConj_of_cycleType_eq
    exact (rep_cycleType 1 ⟨t.cycleType.card, by omega⟩).trans hc.symm
  have hh := rep_cubic 1 ⟨t.cycleType.card, by omega⟩ (by
    have hd : t.cycleType.card = 1 ∨ t.cycleType.card = 3 ∨ t.cycleType.card = 2 := by omega
    rcases hd with hd | hd | hd
    · exact Or.inl (Fin.ext hd)
    · exact Or.inr (Or.inl (Fin.ext hd))
    · exact Or.inr (Or.inr ⟨rfl, Fin.ext hd⟩))
  obtain ⟨g, hg⟩ := isConj_iff.mp hrep
  simpa only [Fin.val_zero, Fin.val_one, MulAut.conj_apply, hg] using
    exists_commuting_cubic_map (MulAut.conj g) hh

/-- A nonidentity involution moving at most one dimension in a faithful binary S₆
representation centralizes an element of order three in the derived subgroup. -/
theorem exists_commuting_cubic_six_of_displacement {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Perm (Fin 6)) V) (hρ : Function.Injective ρ)
    (t : Perm (Fin 6)) (ht : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) :
    ∃ c ∈ commutator (Perm (Fin 6)), orderOf c = 3 ∧ Commute c t := by
  apply exists_commuting_cubic_six_of_odd_involution t ht ht2
  intro he
  exact ht (SixLetterTransvections.even_eq_one_of_displacement_le_one ρ hρ t he hr)

end Representation.PermutationTransvectionCubicCentralizer
