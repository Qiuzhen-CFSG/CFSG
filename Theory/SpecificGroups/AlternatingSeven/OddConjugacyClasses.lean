module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Odd-order conjugacy classes of A₇

An odd-order permutation on seven points has cycle type `0`, `(3)`, `(3,3)`,
`(5)`, or `(7)`: every nontrivial cycle has odd length at least three, and the
lengths sum to at most seven. The first four symmetric-group classes do not
split in A₇. For `0`, `(3)`, and `(5)`, two fixed points give an odd centralizer
element; for `(3,3)`, the repeated cycle length does so. Multiplying an odd
conjugator by that element makes it even. For the remaining type, the two
possible signs of a conjugator give at most two A₇ classes. Thus there are at
most six odd-order classes, for Mathlib's actual group and conjugacy quotient.

This is the group-theoretic class bound used to exhaust the six absolutely
irreducible candidates in characteristic two in the A₇ small-degree argument.
Source context: Aschbacher–Smith, *The Classification of Quasithin Groups*,
K.1.2, printed p.452/PDF p.463. The proof here uses permutation cycle types and
centralizers, independently of the character and decomposition tables cited
there. The centralizer criteria are Mathlib's
`card_le_of_centralizer_le_alternating` and
`count_le_one_of_centralizer_le_alternating`.
-/

public section

open Equiv
namespace alternatingGroup.SevenOddConjugacyClasses

private theorem small_odd_multiset (m : Multiset ℕ) (hs : m.sum ≤ 7)
    (hm : ∀ n ∈ m, 3 ≤ n ∧ n % 2 = 1) :
    m = 0 ∨ m = {3} ∨ m = {3, 3} ∨ m = {5} ∨ m = {7} := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
    have ha := hm a (by simp)
    have hb : a + m.sum ≤ 7 := by simpa using hs
    have hm' : ∀ n ∈ m, 3 ≤ n ∧ n % 2 = 1 := fun n hn => hm n (by simp [hn])
    have h := ih (by omega) hm'
    have ha' : a = 3 ∨ a = 5 ∨ a = 7 := by omega
    rcases ha' with rfl | rfl | rfl <;>
      rcases h with rfl | rfl | rfl | rfl | rfl <;> norm_num at hb
    all_goals norm_num

/-- The five possible nontrivial-cycle multisets of an odd-order element of A₇. -/
theorem cycleType_of_odd_order (g : alternatingGroup (Fin 7)) (hg : ¬ 2 ∣ orderOf g) :
    (g : Perm (Fin 7)).cycleType = 0 ∨
    (g : Perm (Fin 7)).cycleType = {3} ∨
    (g : Perm (Fin 7)).cycleType = {3, 3} ∨
    (g : Perm (Fin 7)).cycleType = {5} ∨
    (g : Perm (Fin 7)).cycleType = {7} := by
  apply small_odd_multiset
  · simpa using (g : Perm (Fin 7)).sum_cycleType_le
  · intro n hn
    have hmin := Perm.two_le_of_mem_cycleType hn
    have hnodd : ¬ 2 ∣ n := fun h => hg <| (h.trans (Perm.dvd_of_mem_cycleType hn)).trans
      (Subgroup.orderOf_coe g).dvd
    simp only [Nat.dvd_iff_mod_eq_zero] at hnodd
    omega

private theorem conj_of_odd_centralizer {α : Type*} [Fintype α] [DecidableEq α]
    {x y : alternatingGroup α} (hxy : IsConj (x : Perm α) (y : Perm α))
    (hc : ¬ Subgroup.centralizer {(x : Perm α)} ≤ alternatingGroup α) : IsConj x y := by
  obtain ⟨p, hp⟩ := isConj_iff.mp hxy
  rcases Int.units_eq_one_or (Perm.sign p) with he | ho
  · apply isConj_iff.mpr
    refine ⟨⟨p, Perm.mem_alternatingGroup.mpr he⟩, Subtype.ext ?_⟩
    exact hp
  · change ¬ ∀ c, c ∈ Subgroup.centralizer {(x : Perm α)} → c ∈ alternatingGroup α at hc
    push Not at hc
    obtain ⟨c, hc, hcodd⟩ := hc
    have hcs : Perm.sign c = -1 := (Int.units_eq_one_or (Perm.sign c)).resolve_left
      (fun h => hcodd (Perm.mem_alternatingGroup.mpr h))
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hc
    apply isConj_iff.mpr
    refine ⟨⟨p * c, Perm.mem_alternatingGroup.mpr (by simp [ho, hcs])⟩, Subtype.ext ?_⟩
    change (p * c) * (x : Perm α) * (p * c)⁻¹ = (y : Perm α)
    calc
      _ = p * (c * (x : Perm α)) * c⁻¹ * p⁻¹ := by group
      _ = p * ((x : Perm α) * c) * c⁻¹ * p⁻¹ := by rw [hcomm]
      _ = (y : Perm α) := by simpa [mul_assoc] using hp

private def twist (x : alternatingGroup (Fin 7)) : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * (x : Perm (Fin 7)) * (swap 0 1)⁻¹, by
    rw [Perm.mem_alternatingGroup]
    simp [Perm.mem_alternatingGroup.mp x.property]⟩

private theorem conj_or_twist {x y : alternatingGroup (Fin 7)}
    (hxy : IsConj (x : Perm (Fin 7)) (y : Perm (Fin 7))) :
    IsConj x y ∨ IsConj (twist x) y := by
  obtain ⟨p, hp⟩ := isConj_iff.mp hxy
  rcases Int.units_eq_one_or (Perm.sign p) with he | ho
  · left
    exact isConj_iff.mpr ⟨⟨p, Perm.mem_alternatingGroup.mpr he⟩, Subtype.ext hp⟩
  · right
    apply isConj_iff.mpr
    refine ⟨⟨p * (swap 0 1)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · rw [Perm.mem_alternatingGroup]
      simp [ho, Perm.sign_swap (show (0 : Fin 7) ≠ 1 by decide)]
    · change (p * (swap 0 1)⁻¹) *
        (swap 0 1 * (x : Perm (Fin 7)) * (swap 0 1)⁻¹) *
        (p * (swap 0 1)⁻¹)⁻¹ = (y : Perm (Fin 7))
      simpa [mul_assoc] using hp

private def classesOfType (m : Multiset ℕ) : Set (ConjClasses (alternatingGroup (Fin 7))) :=
  ConjClasses.mk '' {x : alternatingGroup (Fin 7) | (x : Perm (Fin 7)).cycleType = m}

private theorem classesOfType_finite (m : Multiset ℕ) : (classesOfType m).Finite :=
  (Set.toFinite _).image _

private theorem class_count_le_one (m : Multiset ℕ)
    (h : ∀ x : alternatingGroup (Fin 7), (x : Perm (Fin 7)).cycleType = m →
      ¬ Subgroup.centralizer {(x : Perm (Fin 7))} ≤ alternatingGroup (Fin 7)) :
    (classesOfType m).ncard ≤ 1 := by
  apply (Set.ncard_le_one (classesOfType_finite m)).mpr
  rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (conj_of_odd_centralizer
    (Perm.isConj_iff_cycleType_eq.mpr (hx.trans hy.symm)) (h x hx))

private theorem class_count_le_two (m : Multiset ℕ) : (classesOfType m).ncard ≤ 2 := by
  obtain h | ⟨a, x, hx, rfl⟩ := (classesOfType m).eq_empty_or_nonempty
  · simp [h]
  have hsub : classesOfType m ⊆ {ConjClasses.mk x, ConjClasses.mk (twist x)} := by
    rintro b ⟨y, hy, rfl⟩
    have hc := conj_or_twist (Perm.isConj_iff_cycleType_eq.mpr (hx.trans hy.symm))
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
      ConjClasses.mk_eq_mk_iff_isConj] using hc.imp IsConj.symm IsConj.symm
  apply (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
  simpa using Set.ncard_insert_le (ConjClasses.mk x) {ConjClasses.mk (twist x)}

private theorem small_class_count_le_one (m : Multiset ℕ)
    (hm : m = 0 ∨ m = {3} ∨ m = {3, 3} ∨ m = {5}) :
    (classesOfType m).ncard ≤ 1 := by
  apply class_count_le_one
  intro x hx hc
  rcases hm with rfl | rfl | rfl | rfl
  · have h := Perm.card_le_of_centralizer_le_alternating hc
    norm_num [hx] at h
  · have h := Perm.card_le_of_centralizer_le_alternating hc
    norm_num [hx] at h
  · have h := Perm.count_le_one_of_centralizer_le_alternating hc 3
    norm_num [hx] at h
  · have h := Perm.card_le_of_centralizer_le_alternating hc
    norm_num [hx] at h

/-- A₇ has at most six conjugacy classes consisting of odd-order elements. -/
theorem odd_class_count_le_six :
    Nat.card (ConjClasses.mk '' {g : alternatingGroup (Fin 7) | ¬ 2 ∣ orderOf g}) ≤ 6 := by
  have hsub : (ConjClasses.mk '' {g : alternatingGroup (Fin 7) | ¬ 2 ∣ orderOf g}) ⊆
      classesOfType 0 ∪ classesOfType {3} ∪ classesOfType {3, 3} ∪
        classesOfType {5} ∪ classesOfType {7} := by
    rintro a ⟨g, hg, rfl⟩
    rcases cycleType_of_odd_order g hg with h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨g, h, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨g, h, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨g, h, rfl⟩))
    · exact Or.inl (Or.inr ⟨g, h, rfl⟩)
    · exact Or.inr ⟨g, h, rfl⟩
  have hfin := ((((classesOfType_finite 0).union (classesOfType_finite {3})).union
    (classesOfType_finite {3, 3})).union (classesOfType_finite {5})).union
    (classesOfType_finite {7})
  have hbound := Set.ncard_le_ncard hsub hfin
  have h0 := small_class_count_le_one 0 (Or.inl rfl)
  have h3 := small_class_count_le_one {3} (Or.inr (Or.inl rfl))
  have h33 := small_class_count_le_one {3, 3} (Or.inr (Or.inr (Or.inl rfl)))
  have h5 := small_class_count_le_one {5} (Or.inr (Or.inr (Or.inr rfl)))
  have h7 := class_count_le_two {7}
  have hu3 := Set.ncard_union_le (classesOfType 0) (classesOfType {3})
  have hu33 := Set.ncard_union_le (classesOfType 0 ∪ classesOfType {3})
    (classesOfType {3, 3})
  have hu5 := Set.ncard_union_le (classesOfType 0 ∪ classesOfType {3} ∪ classesOfType {3, 3})
    (classesOfType {5})
  have hu7 := Set.ncard_union_le
    (classesOfType 0 ∪ classesOfType {3} ∪ classesOfType {3, 3} ∪ classesOfType {5})
    (classesOfType {7})
  rw [Nat.card_coe_set_eq]
  omega

end alternatingGroup.SevenOddConjugacyClasses
