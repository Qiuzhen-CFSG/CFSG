module

public import Theory.GroupTheory.ElementaryThirtyTwoThreeSubgroups
public import Theory.GroupTheory.ElementaryThirtyTwoThreeNormalizer
public import Theory.GroupTheory.ElementaryThirtyTwoNineNormalizer
public import Theory.PGroupCore

/-!
# Trivial three-core on an elementary thirty-two

A nontrivial three-core in an automorphism subgroup of an elementary abelian
group of order thirty-two maps to an ambient subgroup of order three or nine.
Its ambient normalizer contains the whole automorphism subgroup. Thus, when
64 divides the latter's order, it also divides that normalizer's order.

The normalizers of subgroups of orders three and nine have orders not divisible
by 64, so the three-core is trivial. This needs neither solvability nor a
restriction on the odd part of the automorphism subgroup order.
Source: Parrott, "A Characterization of the Tits' Simple Group" (1972),
printed p.673, properties (1) and (4), and their use on p.677 after Lemma 5.
-/

open Subgroup

/-- A nontrivial three-core forces an order-three or order-nine normalizer
whose cardinality is divisible by 64. -/
public theorem exists_three_or_nine_normalizer_of_ne_bot_three_core
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (B : Subgroup (MulAut E))
    (hB : 64 ∣ Nat.card B) (hcore : pCore 3 B ≠ ⊥) :
    ∃ A : Subgroup (MulAut E), (Nat.card A = 3 ∨ Nat.card A = 9) ∧
      B ≤ normalizer (A : Set (MulAut E)) ∧
      64 ∣ Nat.card (normalizer (A : Set (MulAut E))) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A := (pCore 3 B).map B.subtype
  have hp : IsPGroup 3 A := (pCore_isPGroup (p := 3) (G := B)).map B.subtype
  have hdiv := card_three_subgroup_dvd_nine_of_elementary_thirtytwo hE A hp
  have hne : Nat.card A ≠ 1 := by
    intro h
    rw [card_map_of_injective B.subtype_injective] at h
    exact hcore (Subgroup.card_eq_one.mp h)
  have hcard : Nat.card A = 3 ∨ Nat.card A = 9 := by
    obtain ⟨k, hk, hpow⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card A ∣ 3 ^ 2 from hdiv)
    interval_cases k
    · exact (hne hpow).elim
    · exact Or.inl hpow
    · exact Or.inr hpow
  have hle : B ≤ normalizer (A : Set (MulAut E)) := by
    have h := (pCore 3 B).le_normalizer_map B.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, B.range_subtype] using h
  exact ⟨A, hcard, hle, hB.trans (card_dvd_of_le hle)⟩

/-- An automorphism subgroup of an elementary abelian group of order thirty-two
has trivial three-core whenever its order is divisible by sixty-four. -/
public theorem three_core_eq_bot_of_elementary_thirtytwo
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (B : Subgroup (MulAut E))
    (hB : 64 ∣ Nat.card B) : pCore 3 B = ⊥ := by
  by_contra hcore
  obtain ⟨A, hA, _, hdiv⟩ :=
    exists_three_or_nine_normalizer_of_ne_bot_three_core hE B hB hcore
  rcases hA with hthree | hnine
  · exact not_sixtyfour_dvd_card_normalizer_of_elementary_thirtytwo_three hE A hthree hdiv
  · exact not_sixtyfour_dvd_card_normalizer_of_elementary_thirtytwo_nine hE A hnine hdiv
