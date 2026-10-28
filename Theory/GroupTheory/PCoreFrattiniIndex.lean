module

public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.ElementaryEightSolvableCore
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# Sylow index over a core with small Frattini quotient

For a finite solvable group with self-centralizing two-core, a Frattini
quotient of order at most eight forces that core to have index at most two
in a Sylow subgroup. The faithful action modulo the core has trivial
two-core. A solvable subgroup of the automorphism group of an elementary
eight whose order is divisible by four has nontrivial two-core, excluding
that case. The smaller elementary quotients have automorphism order dividing six.

This Burnside--Frattini reduction supplies the index calculation used in
Janko–Thompson, Math. Z. 113 (1970), §4, pp.392–393.
-/

open Subgroup

private theorem small_elementary_aut_card_dvd_six
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (k : ℕ) (hk : k ≤ 2) (hV : Nat.card V = 2 ^ k) :
    Nat.card (MulAut V) ∣ 6 := by
  interval_cases k
  · have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp (by simpa using hV)).1
    have : Subsingleton (MulAut V) := ⟨fun a b => MulEquiv.ext (fun _ => Subsingleton.elim _ _)⟩
    rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩]
    decide
  · have hc : Nat.card V = 2 := by simpa using hV
    let : IsCyclic V := isCyclic_of_prime_card hc
    rw [IsCyclic.card_mulAut, hc]
    decide
  · have hc : Nat.card V = 4 := by simpa using hV
    let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    let : IsKleinFour V := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
    rw [IsKleinFour.card_mulAut V]

/-- A self-centralizing two-core with Frattini quotient of order at most eight
has index at most two in every Sylow two-subgroup of a finite solvable group. -/
public theorem Sylow.relIndex_pCore_le_two_of_frattini_card_le_eight
    {K : Type*} [Group K] [Finite K] [Group.IsSolvable K]
    (hcentral : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hbound : Nat.card (pCore 2 K ⧸ frattini (pCore 2 K)) ≤ 8)
    (T : Sylow 2 K) : (pCore 2 K).relIndex T ≤ 2 := by
  let Q := pCore 2 K
  have hQ : IsPGroup 2 Q := pCore_isPGroup
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let V := Q ⧸ frattini Q
  let : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini (p := 2)
  let action : K →* MulAut V := (quotientAut (frattini Q)).comp MulAut.conjNormal
  have hker : action.ker = Q := pCore_frattini_action_kernel 2 hcentral
  let : Group.IsSolvable action.range :=
    Group.isSolvable_of_surjective action.rangeRestrict_surjective
  have hcore : Nat.card (pCore 2 action.range) = 1 := by
    have hh := action.rangeRestrict.card_pCore_of_ker_isPGroup
      action.rangeRestrict_surjective (by
        rw [MonoidHom.ker_rangeRestrict, hker]
        exact hQ)
    rw [MonoidHom.ker_rangeRestrict, hker] at hh
    have hpos : 0 < Nat.card Q := Nat.card_pos
    change Nat.card Q = Nat.card Q * Nat.card (pCore 2 action.range) at hh
    nlinarith
  have hnotfour : ¬ 4 ∣ Nat.card action.range := by
    intro hfour
    obtain ⟨k, hk⟩ := (hQ.to_quotient (frattini Q)).exists_card_eq
    change Nat.card V = 2 ^ k at hk
    have hkle : k ≤ 3 := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      simpa only [← hk] using hbound
    by_cases hsmall : k ≤ 2
    · have hdiv : Nat.card (MulAut V) ∣ 6 := small_elementary_aut_card_dvd_six k hsmall hk
      exact (by decide : ¬ 4 ∣ 6) (hfour.trans (action.range.card_subgroup_dvd_card.trans hdiv))
    · have hV : Nat.card V = 8 := by rw [hk, show k = 3 by omega]; decide
      have hh := four_le_card_pCore_of_solvable_elementary_eight_automorphisms V hV action.range hfour
      omega
  let U := T.mapSurjective action.rangeRestrict_surjective
  have hindex : Q.relIndex T = Nat.card U := by
    have hh := relIndex_ker (K := (T : Subgroup K)) action.rangeRestrict
    rwa [MonoidHom.ker_rangeRestrict, hker] at hh
  rw [hindex]
  obtain ⟨n, hn⟩ := U.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    apply hnotfour
    have hdiv : 4 ∣ Nat.card U := hn ▸ pow_dvd_pow 2 hh
    exact hdiv.trans (U : Subgroup action.range).card_subgroup_dvd_card
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hnle

