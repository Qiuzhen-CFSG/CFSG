module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.SpecificGroups.OddThreeRank
public import Theory.Quasithin.Rank
public import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Quotients and field parameters for the signed model intersection

For a quasisimple group with trivial odd core, the two-core is the center,
so the quotient is simple and quasisimple. In the simple branch the two-core
is trivial, and the supplied signed quotient model lifts without changing
its sign or field order. A cyclic center of order three is incompatible
with trivial odd core; this removes the triple covers in the alternating
action alternatives, without removing central two-covers.

Every signed field parameter is a prime power, including the square-root
parameter in the unitary definition. Thus an even parameter is a positive
power of two. Odd parameters have two-rank at most two: the special matrix
groups have this bound, and their scalar kernels have odd order. Consequently
a two-rank lower bound of three suffices to recover characteristic two.

These are deductions for the model intersection, not the missing comparison
of the complete 1.1.5 list. The latter remains an input of the assembly.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18(2)
(printed pp.51--52), 1.1.5(3) (pp.501--503), and pp.1135, 1139.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
open Chapter1.Section02.LocalModels
variable {K H : Type*} [Group K] [Group H] {unitary : Bool} {q : ℕ}

/-- Transport the supplied sign and exact field order across an actual isomorphism. -/
theorem signed_transport (h : IsPSLSign K unitary 3 q) (e : H ≃* K) :
    IsPSLSign H unitary 3 q := by
  cases unitary with
  | false => exact h.of_mulEquiv e
  | true => exact h.of_mulEquiv e

/-- The fixed-field parameter is a prime power for either sign. -/
theorem signed_parameter_primePower (h : IsPSLSign K unitary 3 q) : IsPrimePow q := by
  cases unitary with
  | false =>
    obtain ⟨F, hF, hfin, hc, _⟩ := h
    let := Fintype.ofFinite F
    simpa only [← Nat.card_eq_fintype_card, hc] using FiniteField.isPrimePow_card F
  | true =>
    obtain ⟨F, hF, hfin, _, hc, _, _⟩ := h
    let := Fintype.ofFinite F
    have hp : IsPrimePow (q ^ 2) := by
      simpa only [← Nat.card_eq_fintype_card, hc] using FiniteField.isPrimePow_card F
    exact (isPrimePow_pow_iff (by decide : 2 ≠ 0)).mp hp

/-- Evenness recovers a positive binary exponent without changing the parameter. -/
theorem signed_parameter_binary (h : IsPSLSign K unitary 3 q) (he : Even q) :
    ∃ n : ℕ, 0 < n ∧ q = 2 ^ n := by
  obtain ⟨p, n, hp, hn, hc⟩ := (isPrimePow_nat_iff q).mp (signed_parameter_primePower h)
  have h2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (hc.symm ▸ even_iff_two_dvd.mp he)
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  exact ⟨n, hn, by simpa [hp2] using hc.symm⟩

/-- Odd field parameters give two-rank at most two, for arbitrary prime powers. -/
theorem signed_odd_twoRank [Finite K] (h : IsPSLSign K unitary 3 q)
    (ho : Odd q) : primeRank 2 K ≤ 2 := by
  cases unitary with
  | false =>
    obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
    rw [primeRank_equiv 2 e]
    have hchar := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card
      ho (k := 1) (by simpa using hc)
    apply (primeRank_le_of_surjective_of_coprime 2 (Matrix.PSL3.projection F)
      (Matrix.PSL3.projection_surjective F) ?_).trans
      (Theory.SpecificGroups.OddThreeRank.special_primeRank_two_le (MulEquiv.refl _) hchar)
    simpa only [Matrix.PSL3.projection_ker] using
      (Matrix.SL3.odd_card_center F).coprime_two_left
  | true =>
    obtain ⟨F, hF, hfin, J, hc, _, ⟨e⟩⟩ := h
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_equiv 2 e]
    have hchar := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hc
    exact (primeRank_le_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective (J.odd_card_specialToProjective_ker).coprime_two_left).trans
      (Theory.SpecificGroups.OddThreeRank.hermitian_special_primeRank_two_le J hchar)

/-- A two-rank lower bound excludes every odd signed field parameter. -/
theorem signed_even_of_twoRank [Finite K] (h : IsPSLSign K unitary 3 q)
    (hr : 3 ≤ primeRank 2 K) : Even q := by
  rcases Nat.even_or_odd q with he | ho
  · exact he
  · have := signed_odd_twoRank h ho
    omega

/-- The two-core vanishes in a finite simple quasisimple group. -/
theorem twoCore_eq_bot_of_simple [Finite K] [IsQuasisimple K] [IsSimpleGroup K] :
    pCore 2 K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 K) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 2 K := by
      have he : IsPGroup 2 (⊤ : Subgroup K) := h ▸ pCore_isPGroup
      exact he.of_equiv Subgroup.topEquiv
    let : Group.IsNilpotent K := hp.isNilpotent
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim

/-- The quotient remains simple even when the original component is a two-cover. -/
theorem twoCore_quotient_simple [Finite K] [IsQuasisimple K]
    (h : pPrimeCore 2 K = ⊥) : IsSimpleGroup (K ⧸ pCore 2 K) := by
  have hz := IsQuasisimple.center_eq_pCore h
  exact ((QuotientGroup.quotientMulEquivOfEq hz).isSimpleGroup_congr).mp IsQuasisimple.simple

/-- The same actual quotient retains quasisimplicity. -/
theorem twoCore_quotient_quasisimple [Finite K] [IsQuasisimple K]
    (h : pPrimeCore 2 K = ⊥) : IsQuasisimple (K ⧸ pCore 2 K) := by
  let := twoCore_quotient_simple h
  exact IsQuasisimple.of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 K))

/-- Lift through a proved trivial two-core; no central cover is collapsed. -/
theorem signed_lift_of_twoCore_eq_bot (hcore : pCore 2 K = ⊥)
    (h : IsPSLSign (K ⧸ pCore 2 K) unitary 3 q) : IsPSLSign K unitary 3 q := by
  exact signed_transport h
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).symm

/-- The simple 1.1.5 alternative permits lifting the signed quotient model. -/
theorem signed_lift_of_simple [Finite K] [IsQuasisimple K] [IsSimpleGroup K]
    (h : IsPSLSign (K ⧸ pCore 2 K) unitary 3 q) : IsPSLSign K unitary 3 q :=
  signed_lift_of_twoCore_eq_bot twoCore_eq_bot_of_simple h

/-- Once evenness is proved, the simple branch has exactly the requested conclusion. -/
theorem simple_binary_conclusion [Finite K] [IsQuasisimple K] [IsSimpleGroup K]
    (h : IsPSLSign (K ⧸ pCore 2 K) unitary 3 q) (he : Even q) :
    ∃ n : ℕ, 0 < n ∧ q = 2 ^ n ∧ IsPSLSign K unitary 3 (2 ^ n) := by
  obtain ⟨n, hn, hq⟩ := signed_parameter_binary h he
  exact ⟨n, hn, hq, hq ▸ signed_lift_of_simple h⟩

/-- A cyclic center of order three lies in the odd core and is therefore excluded. -/
theorem no_center_three (hodd : pPrimeCore 2 K = ⊥)
    (e : center K ≃* Multiplicative (ZMod 3)) : False := by
  have hc : Nat.card (center K) = 3 := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_zmod 3
  have hle : center K ≤ pPrimeCore 2 K := le_sSup ⟨inferInstance, by rw [hc]; decide⟩
  have hz := (center K).card_eq_one.mpr (le_bot_iff.mp (hodd ▸ hle))
  omega

/-- The alternating action alternatives reduce to the actual alternating carriers. -/
theorem alternating_model_of_action (hodd : pPrimeCore 2 K = ⊥)
    {α : MulAut K} {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ComponentStructure.AlternatingAction α n σ) : IsAlternating K n := by
  rcases h with ⟨e, _⟩ | ⟨_, ⟨e⟩, _⟩
  · exact ⟨e⟩
  · exact (no_center_three hodd e).elim

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
