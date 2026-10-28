module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# Centralizers of elements of order three

If nine divides the ambient group order, the centralizer of every element
of order three also has order divisible by nine. Embed its cyclic subgroup
in a Sylow three-subgroup. A centralizer of order at most three there would
coincide with the nontrivial center, making the element central and forcing
the whole Sylow subgroup to have order three.
-/

namespace Subgroup

public theorem nine_dvd_card_centralizer_of_order_three {G : Type*} [Group G] [Finite G]
    (hG : 9 ∣ Nat.card G) (r : G) (hr : orderOf r = 3) :
    9 ∣ Nat.card (centralizer ({r} : Set G)) := by
  by_contra hsmall
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsPGroup 3 (zpowers r) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hr]; rfl)
  obtain ⟨Q, hQ⟩ := hcyc.exists_le_sylow
  let q : Q := ⟨r, hQ (mem_zpowers r)⟩
  let D := centralizer ({q} : Set Q)
  have hD : Nat.card D ∣ 3 := by
    have hmap : D.map (Q : Subgroup G).subtype ≤ centralizer ({r} : Set G) := by
      rintro a ⟨b, hb, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hb))
    have hd := card_dvd_of_le hmap
    rw [card_map_of_injective (Q : Subgroup G).subtype_injective] at hd
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (Q.isPGroup'.to_subgroup D)
    have hnlt : n < 2 := by
      by_contra hnlt
      apply hsmall
      apply dvd_trans _ hd
      rw [hn]
      exact Nat.pow_dvd_pow 3 (by omega : 2 ≤ n)
    rw [hn]
    exact Nat.pow_dvd_pow 3 (by omega : n ≤ 1)
  have h9Q : 9 ∣ Nat.card Q := Q.pow_dvd_card_of_pow_dvd_card (n := 2) hG
  let : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide : 1 < 9) (Nat.le_of_dvd Nat.card_pos h9Q))
  let : Nontrivial (center Q) := Q.isPGroup'.center_nontrivial
  have hZD : center Q ≤ D := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp ha q).symm
  have hZcard : Nat.card (center Q) = 3 := by
    have hd := (card_dvd_of_le hZD).trans hD
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h | h
    · have := Finite.one_lt_card (α := center Q); omega
    · exact h
  have hZD' : center Q = D := eq_of_le_of_card_ge hZD (by
    rw [hZcard]; exact Nat.le_of_dvd (by decide) hD)
  have hqZ : q ∈ center Q := hZD' ▸ mem_centralizer_singleton_iff.mpr rfl
  have hDtop : D = ⊤ := by
    apply top_unique
    intro a _
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hqZ a)
  rw [hDtop, card_top] at hD
  have hh := h9Q.trans hD
  norm_num at hh

end Subgroup
