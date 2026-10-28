module

public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# A three-part bound from a small two-core Frattini quotient

If a finite group's two-core is self-centralizing and its Frattini quotient
has order at most 32, then 27 does not divide the group order. The canonical
Frattini action has kernel exactly the two-core. Its image embeds in a binary
general linear group of dimension at most five, whose order is not divisible
by 27. Removing the two-group kernel gives the same exclusion for the group.

This is a Burnside--Frattini and general-linear-order reduction for the
involution centralizer bound needed in Thompson VI, printed p.630. It does
not assert that the relevant terminal core has this small Frattini quotient.
-/

open Subgroup

/-- A self-centralizing two-core with Frattini quotient of order at most 32
forces the three-part of the whole group order to be at most nine. -/
public theorem not_twentyseven_dvd_card_of_characteristic_two_frattini_le_thirtytwo
    {G : Type*} [Group G] [Finite G]
    (hcentral : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hbound : Nat.card (pCore 2 G ⧸ frattini (pCore 2 G)) ≤ 32) :
    ¬ 27 ∣ Nat.card G := by
  let Q := pCore 2 G
  have hQ : IsPGroup 2 Q := pCore_isPGroup
  let _ : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let V := Q ⧸ frattini Q
  change Nat.card V ≤ 32 at hbound
  let _ : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini (p := 2)
  let action : G →* MulAut V := (quotientAut (frattini Q)).comp MulAut.conjNormal
  have hker : action.ker = Q := pCore_frattini_action_kernel 2 hcentral
  have hcount : Nat.card Q * Nat.card action.range = Nat.card G := by
    rw [← index_ker, hker]
    exact Q.card_mul_index
  obtain ⟨n, hn⟩ := (hQ.to_quotient (frattini Q)).exists_card_eq
  have hnle : n ≤ 5 := by
    by_contra! h
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) h
    rw [← hn] at hp
    norm_num at hp
    exact (by omega : ¬ 64 ≤ Nat.card V) hp
  have hAut : ¬ 27 ∣ Nat.card (MulAut V) := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow V n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hcoprime : Nat.Coprime 27 (Nat.card Q) := by
    rw [hk]
    exact (by decide : Nat.Coprime 27 2).pow_right k
  intro h
  rw [← hcount] at h
  exact hAut ((hcoprime.dvd_of_dvd_mul_left h).trans
    action.range.card_subgroup_dvd_card)
