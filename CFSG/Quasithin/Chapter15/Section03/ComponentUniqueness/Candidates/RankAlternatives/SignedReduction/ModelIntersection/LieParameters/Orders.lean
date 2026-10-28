module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.Basic
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.SU3.PrimeOrderDivisibility
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
/-!
# Defining-prime cubes in the signed model intersection

Both PSL₃(q) and PSU₃(q) have order divisible by q³. For the unitary
carrier this follows from its actual upper root subgroup, after transporting
the prescribed Frobenius form to the standard form. If the group order divides
2¹¹ · 3³ · 5² · 7 · 13, its only possible defining primes are two and three.
The signed congruence excludes three. This single checked order test handles
PSL₂(4), PSL₃(2), PSU₃(4), Sp₄(2)′, G₂(2)′, PSL₄(2), and the Tits group.

These are order obstructions, without recognition from equal orders.
Source: Aschbacher--Smith, 1.1.5(3), printed pp.501--503, intersected with
A.3.18(2), pp.51--52, in 15.3.37 and 15.3.43, pp.1135 and 1139.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
open Chapter1.Section02.LocalModels
variable {S : Type*} [Group S] {unitary : Bool} {q : ℕ}

/-- The supplied fixed-field parameter contributes its full cube to the group order. -/
theorem signed_parameter_cube_dvd (h : IsPSLSign S unitary 3 q) :
    q ^ 3 ∣ Nat.card S := by
  have hpp := signed_parameter_primePower h
  cases unitary with
  | false =>
    obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv, ← hc]
    exact Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card
  | true =>
    obtain ⟨F, hF, hfin, J, hc, hconj, ⟨e⟩⟩ := h
    obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp hpp
    let : Fact p.Prime := ⟨hp⟩
    have hfixed : Nat.card {x : F // J.conj x = x} = q := by
      rw [← hpn] at hc hconj ⊢
      exact FiniteField.card_fixed_of_quadratic_frobenius J.conj p n hn hc hconj
    open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter in
      obtain ⟨e'⟩ := FormTransport.exists_projectiveEquiv J q hc hfixed
    rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv]
    open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter in
      have hr := Coverage.rootGroup_card (FormTransport.standardForm J) rfl q hc hfixed
    rw [← hr]
    exact card_subgroup_dvd_card _

/-- The common order bound for the small Lie endpoints forces evenness. -/
theorem signed_even_of_small_order (h : IsPSLSign S unitary 3 q)
    (hmod : q % 3 = (if unitary then 2 else 1))
    (hc : Nat.card S ∣ 125798400) : Even q := by
  obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp (signed_parameter_primePower h)
  have hpq : p ∣ q := hpn ▸ dvd_pow_self p (by omega : n ≠ 0)
  have hp3 : p ≠ 3 := by
    intro he
    have := Nat.dvd_iff_mod_eq_zero.mp (he ▸ hpq)
    cases unitary <;> simp_all
  have hcube : p ^ 3 ∣ 125798400 :=
    (pow_dvd_pow_of_dvd hpq 3).trans ((signed_parameter_cube_dvd h).trans hc)
  have hd : p ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 7 * 13 := by
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hcube
  simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 11 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 2 ≠ 0), Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)] at hd
  rcases hd with (((he | he) | he) | he) | he
  · exact even_iff_two_dvd.mpr (he ▸ hpq)
  · exact (hp3 he).elim
  all_goals subst p; norm_num at hcube
end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
