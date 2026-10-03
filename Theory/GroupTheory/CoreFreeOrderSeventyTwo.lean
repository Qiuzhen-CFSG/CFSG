module

public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# The three-part of a two-core-free group of order dividing 72

If four divides the order, nine must also divide it. Otherwise the Sylow
two-subgroup has index one or three. Index one contradicts the trivial
core; the action on three cosets at index three identifies the core
quotient with the symmetric group of degree three, again contradicting
four-divisibility.

This supplies the order-nine step for the quaternion central-product
outer action in Janko–Thompson (1970), §4, printed p.390.
-/

open Subgroup

/-- Four-divisibility forces the full three-part in a two-core-free group
whose order divides 72. No solvability hypothesis is required. -/
public theorem nine_dvd_card_of_twoCore_eq_bot_of_card_dvd_seventy_two
    {K : Type*} [Group K] [Finite K]
    (hcore : pCore 2 K = ⊥) (hcard : Nat.card K ∣ 72)
    (hfour : 4 ∣ Nat.card K) : 9 ∣ Nat.card K := by
  classical
  by_contra hnine
  have h24 : Nat.card K ∣ 24 := by
    have hmem : Nat.card K ∈ (72 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hcard, by decide⟩
    have hds : (72 : ℕ).divisors = {1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72} := by decide
    rw [hds] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp_all
  let T : Sylow 2 K := Classical.choice inferInstance
  have hidx : (T : Subgroup K).index = 1 ∨ (T : Subgroup K).index = 3 := by
    have hd := T.index_dvd_card.trans h24
    have hmem : (T : Subgroup K).index ∈ (24 : ℕ).divisors :=
      Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have hodd := T.not_dvd_index
    have hds : (24 : ℕ).divisors = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
    rw [hds] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h <;> simp_all
  have hproper : pCore 2 K < (T : Subgroup K) := by
    have hle := pCore_isPGroup.le_sylow_of_normal T
    apply lt_of_le_of_ne hle
    intro heq
    have hbot : (T : Subgroup K) = ⊥ := heq.symm.trans hcore
    have hc : Nat.card T = 1 := by rw [hbot]; exact card_bot
    have hmul := (T : Subgroup K).card_mul_index
    rw [hc, one_mul] at hmul
    rcases hidx with h | h <;> rw [h] at hmul <;>
      rw [← hmul] at hfour <;> norm_num at hfour
  rcases hidx with hone | hthree
  · have htop : (T : Subgroup K) = ⊤ := index_eq_one.mp hone
    have hn : (T : Subgroup K).Normal := htop ▸ inferInstance
    exact (not_le_of_gt hproper) (le_sSup ⟨hn, T.isPGroup'⟩)
  · obtain ⟨e⟩ := sylow_index_three_core_quotient T hthree hproper
    have hc : Nat.card (K ⧸ pCore 2 K) = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      decide
    have hmul := (pCore 2 K).card_mul_index
    rw [hcore, card_bot, one_mul] at hmul
    change Nat.card (K ⧸ pCore 2 K) = 6 at hc
    rw [hcore] at hc
    change (⊥ : Subgroup K).index = 6 at hc
    rw [hmul] at hc
    simp_all
