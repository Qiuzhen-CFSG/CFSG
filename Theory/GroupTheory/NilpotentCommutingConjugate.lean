module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup

/-!
# Commuting conjugates from normalizer growth

A noncentral element of a nilpotent group has a distinct commuting conjugate:
its proper centralizer lies strictly inside its normalizer. For an involution
normalizing a two-subgroup Q, apply this to Q⟨r⟩ and remove the power of r
from the conjugator. The resulting conjugator belongs to Q itself.

This is the elementary two-group step used after Aschbacher–Smith 16.1.6
in the proof of 16.4.9(2), printed p.1190 (1 March 2004 manuscript).
-/

public section

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory

/-- Normalizer growth gives a distinct commuting conjugate of a noncentral
 element of a nilpotent group. -/
theorem exists_distinct_commuting_conjugate_of_nilpotent
    {P : Type*} [Group P] [Group.IsNilpotent P] {r : P}
    (hr : r ∉ center P) : ∃ x : P, MulAut.conj x r ≠ r ∧ Commute r (MulAut.conj x r) := by
  let C := centralizer ({r} : Set P)
  have hC : C < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    apply hr
    apply mem_center_iff.mpr
    intro y
    have hy : y ∈ C := he ▸ mem_top y
    exact mem_centralizer_singleton_iff.mp hy
  obtain ⟨x, hxN, hxC⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent C hC)
  have hrC : r ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hsC : MulAut.conj x r ∈ C := (mem_normalizer_iff.mp hxN r).mp hrC
  refine ⟨x, ?_, (mem_centralizer_singleton_iff.mp hsC).symm⟩
  intro he
  apply hxC
  apply mem_centralizer_singleton_iff.mpr
  exact mul_inv_eq_iff_eq_mul.mp he

/-- If an involution acts nontrivially on a finite two-subgroup Q that it
normalizes, a Q-conjugate distinct from it commutes with it. -/
theorem exists_distinct_commuting_conjugate_in_two_subgroup
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    {r : G} (hr2 : orderOf r = 2) (hrN : r ∈ normalizer (Q : Set G))
    (hrC : r ∉ centralizer (Q : Set G)) :
    ∃ l ∈ Q, MulAut.conj l r ≠ r ∧ Commute r (MulAut.conj l r) := by
  let P := Q ⊔ zpowers r
  have hp : IsPGroup 2 P := hQ.to_sup_of_normal_left'
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one]))
    (zpowers_le.mpr hrN)
  let : Group.IsNilpotent P := hp.isNilpotent
  let rP : P := ⟨r, mem_sup_right (mem_zpowers r)⟩
  have hrZ : rP ∉ center P := by
    intro hz
    apply hrC
    intro q hq
    exact congrArg Subtype.val (mem_center_iff.mp hz (⟨q, mem_sup_left hq⟩ : P))
  obtain ⟨x, hne, hc⟩ := exists_distinct_commuting_conjugate_of_nilpotent hrZ
  have hx : (x : G) ∈ (↑Q : Set G) * (↑(zpowers r) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr hrN)]
    exact x.property
  obtain ⟨l, hl, a, ha, he⟩ := hx
  have haC : a ∈ centralizer ({r} : Set G) := by
    apply (show zpowers r ≤ centralizer ({r} : Set G) from
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) ha
  have har : a * r * a⁻¹ = r := by
    rw [mem_centralizer_singleton_iff.mp haC, mul_inv_cancel_right]
  have hconj : ((MulAut.conj x rP : P) : G) = MulAut.conj l r := by
    change (x : G) * r * (x : G)⁻¹ = l * r * l⁻¹
    rw [← he, mul_inv_rev]
    calc
      l * a * r * (a⁻¹ * l⁻¹) = l * (a * r * a⁻¹) * l⁻¹ := by group
      _ = l * r * l⁻¹ := by rw [har]
  refine ⟨l, hl, ?_, ?_⟩
  · intro hh
    exact hne (Subtype.ext (hconj.trans hh))
  · have h := congrArg Subtype.val hc.eq
    change r * ((MulAut.conj x rP : P) : G) = ((MulAut.conj x rP : P) : G) * r at h
    rw [hconj] at h
    exact h

end Theory.GroupTheory
