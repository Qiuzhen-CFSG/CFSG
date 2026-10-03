module

public import Theory.GroupTheory.CharacteristicTwoSolvableCoreLowerBound
public import Theory.GroupTheory.ElementaryThirtyTwoThirtyOneNormalizer
public import Theory.GroupTheory.ElementaryThirtyTwoThreeCore
public import Theory.GroupTheory.ElementaryThirtyTwoFiveSevenCores

/-!
# The solvable two-core bound on an elementary group of order 32

Orbit counting restricts the prime divisors of automorphism subgroup orders
to 2, 3, 5, 7 and 31. A subgroup of order 64n, with 1 ≤ n ≤ 31, has trivial thirty-one core.
Indeed a nontrivial thirty-one core would have order exactly 31 and would
put the whole subgroup inside an odd-order normalizer.

The normalizer restrictions at three, five and seven exclude the remaining
odd prime cores. The solvable Fitting and Frattini argument then gives the
two-core lower bound 16, eliminating the exceptional alternative n = 21.
The bound does not require n to be odd.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
the GL(5,2) properties on p.673 and their use on p.677 after Lemma 5.
-/

open Subgroup

/-- Orbit counting restricts the primes in an automorphism subgroup on a
group of order 32. No linear model or solvability hypothesis is required. -/
public theorem prime_dvd_card_automorphisms_thirtytwo
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 32)
    (B : Subgroup (MulAut E)) {p : ℕ} (hp : p.Prime) (hdiv : p ∣ Nat.card B) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hdiv
  let A := zpowers (a : MulAut E)
  have hA : Nat.card A = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha]
  have hAp : IsPGroup p A := IsPGroup.of_card (n := 1) (by simpa using hA)
  let F := FixedPoints.subgroup A E
  have hmod := hAp.card_modEq_card_fixedPoints E
  change Nat.ModEq p (Nat.card E) (Nat.card F) at hmod
  have hFdiv : Nat.card F ∣ 2 ^ 5 := by simpa [hE] using F.card_subgroup_dvd_card
  obtain ⟨k, hkle, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFdiv
  have hkne : k ≠ 5 := by
    intro heq
    have htop : F = ⊤ := F.eq_top_of_card_eq (by simpa [heq, hE] using hk)
    have haone : (a : MulAut E) = 1 := by
      apply MulEquiv.ext
      intro x
      have hx : x ∈ F := htop ▸ mem_top x
      exact hx ⟨a, mem_zpowers (a : MulAut E)⟩
    have ha' : a = 1 := Subtype.ext haone
    rw [ha', orderOf_one] at ha
    exact hp.ne_one ha.symm
  have hk4 : k ≤ 4 := by omega
  rw [hE, hk] at hmod
  have hpdvd : p ∣ 32 - 2 ^ k :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by decide : 0 < 2) hkle)).mp hmod.symm
  have hcommon : p ∣ 52080 := hpdvd.trans (by interval_cases k <;> decide)
  have hmem : p ∈ (52080 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hcommon, by decide⟩
  have hprimes : (52080 : ℕ).primeFactors = {2, 3, 5, 7, 31} := by
    change (2 ^ 4 * 3 * 5 * 7 * 31 : ℕ).primeFactors = _
    rw [Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_prime_pow (by decide) Nat.prime_two]
    norm_num [show Nat.Prime 3 by decide, show Nat.Prime 5 by decide,
      show Nat.Prime 7 by decide, show Nat.Prime 31 by decide]
  simpa only [hprimes, Finset.mem_insert, Finset.mem_singleton] using hmem

/-- The odd normalizer of a thirty-one subgroup excludes a nontrivial
thirty-one core for these orders, without a solvability hypothesis. -/
public theorem thirtyone_core_eq_bot_of_aut32_card
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (B : Subgroup (MulAut E))
    {n : ℕ} (hnpos : 1 ≤ n) (hnle : n ≤ 31) (hB : Nat.card B = 64 * n) :
    pCore 31 B = ⊥ := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  obtain ⟨j, hj⟩ := (pCore_isPGroup (p := 31) (G := B)).exists_card_eq
  have hdiv : 31 ^ j ∣ n := by
    apply ((show Nat.Coprime 31 64 by decide).pow_left j).dvd_of_dvd_mul_left
    rw [← hB, ← hj]
    exact (pCore 31 B).card_subgroup_dvd_card
  have hbound : 31 ^ j ≤ 31 := (Nat.le_of_dvd (by omega) hdiv).trans hnle
  have hjle : j ≤ 1 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 31) hh
    norm_num at hp
    omega
  by_cases hjzero : j = 0
  · exact Subgroup.card_eq_one.mp (by simpa [hjzero] using hj)
  have hjone : j = 1 := by omega
  have hcard : Nat.card (pCore 31 B) = 31 := by simpa [hjone] using hj
  let A := (pCore 31 B).map B.subtype
  have hA : Nat.card A = 31 := by
    rw [card_map_of_injective B.subtype_injective]
    exact hcard
  have hle : B ≤ normalizer (A : Set (MulAut E)) := by
    have hh := (pCore 31 B).le_normalizer_map B.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, B.range_subtype] using hh
  have hodd : Odd (Nat.card B) :=
    (odd_card_normalizer_of_elementary_thirtytwo_thirtyone E hE A hA).of_dvd_nat
      (card_dvd_of_le hle)
  have htwo : 2 ∣ Nat.card B := by
    rw [hB]
    exact dvd_mul_of_dvd_left (by decide : 2 ∣ 64) n
  exact (hodd.not_two_dvd_nat htwo).elim

/-- The solvable two-core bound reduces to the three remaining prime-core
obstructions, at primes three, five and seven. -/
public theorem sixteen_le_card_two_core_of_aut32_three_five_seven_cores
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (B : Subgroup (MulAut E)) [Group.IsSolvable B]
    {n : ℕ} (hnpos : 1 ≤ n) (hnle : n ≤ 31) (hB : Nat.card B = 64 * n)
    (hthree : pCore 3 B = ⊥) (hfive : pCore 5 B = ⊥) (hseven : pCore 7 B = ⊥) :
    16 ≤ Nat.card (pCore 2 B) := by
  apply sixteen_le_card_two_core_of_solvable_odd_cores_trivial
    (hdiv := by rw [hB]; exact dvd_mul_right 64 n)
  intro p hp hne
  let : Fact p.Prime := ⟨hp⟩
  by_cases hdiv : p ∣ Nat.card B
  · rcases prime_dvd_card_automorphisms_thirtytwo hE B hp hdiv with
      rfl | rfl | rfl | rfl | rfl
    · exact (hne rfl).elim
    · exact hthree
    · exact hfive
    · exact hseven
    · exact thirtyone_core_eq_bot_of_aut32_card hE B hnpos hnle hB
  · apply Subgroup.card_eq_one.mp
    exact (pCore_isPGroup (p := p) (G := B)).card_eq_or_dvd.resolve_right
      (fun hh => hdiv (hh.trans (pCore p B).card_subgroup_dvd_card))

/-- A solvable automorphism subgroup of an elementary abelian group of order
32, of order 64*n with 1 ≤ n ≤ 31, has two-core order at least 16.
In particular the exceptional alternative at n = 21 is unnecessary. -/
public theorem sixteen_le_card_two_core_of_solvable_elementary_thirtytwo_automorphisms
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (B : Subgroup (MulAut E)) [Group.IsSolvable B]
    {n : ℕ} (hnpos : 1 ≤ n) (hnle : n ≤ 31) (hB : Nat.card B = 64 * n) :
    16 ≤ Nat.card (pCore 2 B) := by
  have hdiv : 64 ∣ Nat.card B := by
    rw [hB]
    exact dvd_mul_right 64 n
  obtain ⟨hfive, hseven⟩ :=
    five_seven_cores_eq_bot_of_elementary_thirtytwo_card hE B n hB
  exact sixteen_le_card_two_core_of_aut32_three_five_seven_cores hE B hnpos hnle hB
    (three_core_eq_bot_of_elementary_thirtytwo hE B hdiv) hfive hseven
