module

public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupTheory.ElementaryEightSevenNormalizer
public import Theory.GroupTheory.ElementaryEightThreeNormalizer
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# The two-core of a solvable elementary-eight automizer

A solvable subgroup A of the automorphism group of an elementary abelian group
of order eight has two-core of order at least four whenever four divides |A|.
The statement concerns the actual subgroup and requires no invariant plane.

The ambient order is 168. Its three- and seven-cores, if nontrivial, have
prime order. Normality would put A in the corresponding ambient normalizer,
whose order is not divisible by four. Thus the Fitting subgroup is the two-core.
Solvable Fitting self-centralization excludes order one or two: in either case
the Fitting subgroup is central, so it must be the whole group.

This supplies the intrinsic small-automizer step in the elementary-eight
branch of Stellmacher's local analysis, Journal of Algebra 190 (1997),
Section 11; see `refs/latex/stellmacher-n-group.tex`.
-/

open Subgroup

private theorem core_eq_bot_of_normalizer_obstruction
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 168)
    (A : Subgroup G) (hfour : 4 ∣ Nat.card A)
    (p : ℕ) [Fact p.Prime] (hnot : ¬ p ^ 2 ∣ 168)
    (hnorm : ∀ B : Subgroup G, Nat.card B = p →
      ¬ 4 ∣ Nat.card (normalizer (B : Set G))) : pCore p A = ⊥ := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := A)).exists_card_eq
  have hdiv : p ^ n ∣ 168 := by
    rw [← hn, ← hG]
    exact dvd_trans (pCore p A).card_subgroup_dvd_card A.card_subgroup_dvd_card
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact hnot (dvd_trans (pow_dvd_pow p hh) hdiv)
  by_cases hz : n = 0
  · apply Subgroup.card_eq_one.mp
    simpa only [hz, pow_zero] using hn
  have hn1 : n = 1 := by omega
  have hcard : Nat.card (pCore p A) = p := by simpa only [hn1, pow_one] using hn
  let B := (pCore p A).map A.subtype
  have hB : Nat.card B = p := by
    rw [card_map_of_injective A.subtype_injective]
    exact hcard
  have hle : A ≤ normalizer (B : Set G) := by
    have hh := (pCore p A).le_normalizer_map A.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, A.range_subtype] using hh
  exact (hnorm B hB (dvd_trans hfour (card_dvd_of_le hle))).elim

/-- Four-divisibility forces a two-core of order at least four in a solvable
subgroup of the automorphism group of an elementary abelian group of order eight. -/
public theorem four_le_card_pCore_of_solvable_elementary_eight_automorphisms
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E)) [Group.IsSolvable A]
    (hfour : 4 ∣ Nat.card A) : 4 ≤ Nat.card (pCore 2 A) := by
  have hAut : Nat.card (MulAut E) = 168 := card_mulAut_of_elementary_eight E hE
  have hdiv : Nat.card A ∣ 168 := hAut ▸ A.card_subgroup_dvd_card
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hthree : pCore 3 A = ⊥ := core_eq_bot_of_normalizer_obstruction hAut A hfour 3
    (by decide) (fun B hB => not_four_dvd_card_normalizer_of_elementary_eight_three hE B hB)
  have hseven : pCore 7 A = ⊥ := core_eq_bot_of_normalizer_obstruction hAut A hfour 7
    (by decide) (by
      intro B hB hfourB
      exact (odd_card_normalizer_of_elementary_eight_seven E hE B hB).not_two_dvd_nat
        (dvd_trans (by decide : 2 ∣ 4) hfourB))
  have hfit : fittingSubgroup A = pCore 2 A := by
    apply le_antisymm
    · rw [fitting_eq_sup_pCore]
      refine iSup_le fun p => ?_
      have hpdiv : p.val.val ∣ 168 := dvd_trans
        (Nat.dvd_of_mem_primeFactors p.val.property) hdiv
      have hpmem : p.val.val ∈ (168 : ℕ).primeFactors := Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors p.val.property, hpdiv, by decide⟩
      have hprimes : (168 : ℕ).primeFactors = {2, 3, 7} := by
        change (2 ^ 3 * 3 * 7 : ℕ).primeFactors = _
        rw [Nat.primeFactors_mul (by decide) (by decide),
          Nat.primeFactors_mul (by decide) (by decide),
          Nat.primeFactors_prime_pow (by decide) Nat.prime_two]
        norm_num [show Nat.Prime 3 by decide, show Nat.Prime 7 by decide]
      rw [hprimes] at hpmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpmem
      rcases hpmem with hp | hp | hp
      · rw [hp]
      · rw [hp, hthree]
        exact bot_le
      · rw [hp, hseven]
        exact bot_le
    · exact pCore_le_fitting A 2
  by_contra! hsmall
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hnlt : n < 2 := by
    by_contra! hh
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hn] at hpow
    norm_num at hpow
    omega
  have hcentral : pCore 2 A ≤ center A := by
    interval_cases n
    · have hbot : pCore 2 A = ⊥ := Subgroup.card_eq_one.mp (by simpa using hn)
      rw [hbot]
      exact bot_le
    · exact central_of_normal_card_two (pCore 2 A) (by simpa using hn)
  have hself : centralizer (pCore 2 A : Set A) ≤ pCore 2 A := by
    rw [← hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance
  have htop : pCore 2 A = ⊤ := top_unique <|
    (centralizer_eq_top_iff_subset.mpr hcentral) ▸ hself
  have hA : Nat.card A < 4 := by simpa only [htop, card_top] using hsmall
  exact (not_le_of_gt hA) (Nat.le_of_dvd Nat.card_pos hfour)
