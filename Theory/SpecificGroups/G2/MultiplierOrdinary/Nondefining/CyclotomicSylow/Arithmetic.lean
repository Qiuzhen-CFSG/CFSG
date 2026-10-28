module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.Arithmetic

/-!
# Cyclotomic prime arithmetic for even-characteristic G₂

The checked group order separates primes outside q²−1 into the two cubic
cyclotomic factors. The untwisted factor has a concrete cubic torus, whose
index is prime to the relevant prime. For the twisted factor, q has order
six modulo the prime; this is the degree input for the faithful natural
representation, not a claim that arithmetic alone establishes cyclicity.

Source: the local Sylow argument used in Aschbacher--Smith I.1.2--I.1.4,
printed pp.407--408, and the multiplier calculation cited in GLS III §6.1.
The characteristic-independent index formulas are reused unchanged from
the odd-characteristic development.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow

open OddCyclotomicSylow

variable {F : Type*} [Field F] [Finite F]

/-- The field cardinality has no prime divisors other than two. -/
theorem not_dvd_card_field [CharP F 2] {r : ℕ} [Fact r.Prime] (hr : 3 < r) :
    ¬ r ∣ Nat.card F := by
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  intro h
  have := Nat.le_of_dvd (by decide : 0 < 2) ((Fact.out : r.Prime).dvd_of_dvd_pow h)
  omega

/-- These are precisely the two remaining cyclotomic factors of the actual order. -/
theorem cyclotomic_alternatives [CharP F 2] {r : ℕ} [Fact r.Prime]
    (hr : 3 < r) (hquad : ¬ r ∣ Nat.card F ^ 2 - 1)
    (horder : r ∣ Nat.card (Model F)) :
    r ∣ Nat.card F ^ 2 + Nat.card F + 1 ∨ r ∣ Nat.card F ^ 2 - Nat.card F + 1 := by
  rw [card_model_factorization] at horder
  have hp := (Fact.out : r.Prime)
  have hn : ¬ r ∣ Nat.card F ^ 6 * (Nat.card F ^ 2 - 1) ^ 2 :=
    hp.not_dvd_mul (fun h => not_dvd_card_field hr (hp.dvd_of_dvd_pow h))
      (fun h => hquad (hp.dvd_of_dvd_pow h))
  rcases hp.dvd_mul.mp horder with h | h
  · exact Or.inl ((hp.dvd_mul.mp h).resolve_left hn)
  · exact Or.inr h

private theorem cyclotomic_disjoint {q r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (hd : r ∣ q ^ 2 + q + 1) : ¬ r ∣ q ^ 2 - q + 1 := by
  intro he
  have hp := (Fact.out : r.Prime)
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hdiff : r ∣ 2 * q := by
    convert Nat.dvd_sub hd he using 1; omega
  have hnot2 : ¬ r ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  have hq : r ∣ q := (hp.dvd_mul.mp hdiff).resolve_left hnot2
  have hsum : r ∣ q ^ 2 + q := dvd_add (hq.trans (dvd_pow_self q (by decide))) hq
  apply hp.not_dvd_one
  convert Nat.dvd_sub hd hsum using 1; omega

private theorem sylow_isCyclic_of_cyclic_index {G : Type*} [Group G] [Finite G]
    {r : ℕ} [Fact r.Prime] (C : Subgroup G) [IsCyclic C]
    (hi : ¬ r ∣ C.index) (Q : Sylow r G) : IsCyclic Q := by
  let T : Sylow r C := default
  let A := (T : Subgroup C).map C.subtype
  have ha : IsPGroup r A := T.isPGroup'.map C.subtype
  have hai : ¬ r ∣ A.index := by
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : r.Prime).not_dvd_mul T.not_dvd_index hi
  let U : Sylow r G := ha.toSylow hai
  let e := (T : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective
  have hc : IsCyclic U := e.isCyclic.mp inferInstance
  exact (U.equiv Q).isCyclic.mp hc

/-- A concrete cubic torus contains a full Sylow subgroup at the source prime. -/
theorem sylow_isCyclic_of_cubic_torus [CharP F 2]
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hquad : ¬ r ∣ Nat.card F ^ 2 - 1)
    (hd : r ∣ Nat.card F ^ 2 + Nat.card F + 1)
    (C : Subgroup (Model F)) [IsCyclic C]
    (hc : Nat.card C = Nat.card F ^ 2 + Nat.card F + 1)
    (Q : Sylow r (Model F)) : IsCyclic Q := by
  apply sylow_isCyclic_of_cyclic_index C ?_ Q
  rw [index_of_cubic_card C hc]
  have hp := (Fact.out : r.Prime)
  exact hp.not_dvd_mul
    (hp.not_dvd_mul (fun h => not_dvd_card_field hr (hp.dvd_of_dvd_pow h))
      (fun h => hquad (hp.dvd_of_dvd_pow h))) (cyclotomic_disjoint hr hd)

/-- A prime in the twisted cubic factor and outside q²−1 has field order six. -/
theorem orderOf_card_of_dvd_twisted {r : ℕ} [Fact r.Prime]
    (hr : 3 < r) (hquad : ¬ r ∣ Nat.card F ^ 2 - 1)
    (hd : r ∣ Nat.card F ^ 2 - Nat.card F + 1) :
    orderOf (Nat.card F : ZMod r) = 6 := by
  let q := Nat.card F
  have hq : 1 ≤ q := Nat.card_pos
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hz : (q : ZMod r) ^ 2 - (q : ZMod r) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ r).mpr hd
    change ((q ^ 2 - q + 1 : ℕ) : ZMod r) = 0 at this
    simpa only [Nat.cast_add, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one] using this
  have h3 : (q : ZMod r) ^ 3 = -1 := by
    linear_combination ((q : ZMod r) + 1) * hz
  have h6 : (q : ZMod r) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by decide, pow_mul, h3]
    ring
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) h6
  intro p hp hp6
  rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from hp6) with hp2 | hp3
  · have he : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left hp.ne_one
    subst p
    norm_num only [Nat.reduceDiv]
    intro h
    have hzero : (2 : ZMod r) = 0 := by linear_combination h3 - h
    have hh := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 r).mp hzero)
    omega
  · have he : p = 3 := (Nat.dvd_prime Nat.prime_three).mp hp3 |>.resolve_left hp.ne_one
    subst p
    norm_num only [Nat.reduceDiv]
    intro h
    apply hquad
    apply (ZMod.natCast_eq_zero_iff _ r).mp
    rw [Nat.cast_sub (Nat.one_le_pow 2 q hq), Nat.cast_pow, Nat.cast_one, h, sub_self]

end Atlas.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow
