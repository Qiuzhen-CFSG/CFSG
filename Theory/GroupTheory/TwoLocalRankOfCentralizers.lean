module

public import Theory.Quasithin.LocalRank
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PGroup.ElementaryNormalizer
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# Two-local rank from involution and four-group centralizers

In two-rank at most two, the first Omega subgroup of the center of a
nontrivial two-subgroup has order two or four, and its normalizer contains
the original normalizer. The order-two case is an involution centralizer.
For a four-group, conjugation has centralizer kernel and image in its
six-element automorphism group. Its odd-prime rank contribution is at most
one. These facts reduce local-rank bounds to literal element and subgroup
centralizers, as used in Aschbacher–Smith A.2.12, printed p.36.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem odd_prime_rank_le_one_of_card_six
    {K : Type*} [Group K] [Finite K] (hp : Odd p) (hK : Nat.card K = 6) :
    primeRank p K ≤ 1 := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    have := Nat.odd_iff.mp hp
    omega
  apply (primeRank_le_iff_elementary_card_le K).mpr
  intro A hA
  let : IsElementaryAbelian p A := hA
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
  have hd : p ^ k ∣ 6 := by simpa only [hk,hK] using A.card_subgroup_dvd_card
  have hk1 : k ≤ 1 := by
    by_contra! h
    have hs : p ^ 2 ≤ 6 := Nat.le_of_dvd (by decide)
      ((pow_dvd_pow p (by omega : 2 ≤ k)).trans hd)
    nlinarith
  rw [hk]
  exact pow_le_pow_right' (Fact.out : p.Prime).one_lt.le hk1

/-- In two-rank at most two, involution-centralizer rank e and four-group
centralizer rank one imply the source local bound max 2 e. -/
theorem twoLocalPrimeRank_le_max_of_centralizers
    (hp : Odd p) {e : ℕ} (hr : primeRank 2 G ≤ 2)
    (hi : ∀ t : G, orderOf t = 2 → primeRank p (centralizer ({t} : Set G)) ≤ e)
    (hf : ∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E = 4 →
      primeRank p (centralizer (E : Set G)) ≤ 1) :
    twoLocalPrimeRank p G ≤ max 2 e := by
  apply (twoLocalPrimeRank_le_iff p _).mpr
  rintro N ⟨P,hPne,hP,rfl⟩
  obtain ⟨E,hEne,_,hE,hNE⟩ := P.exists_nontrivial_elementary_with_normalizer_le hP hPne
  apply (primeRank_mono p hNE).trans
  let : IsElementaryAbelian 2 E := hE
  have hE4 : Nat.card E ≤ 4 := (primeRank_le_iff_elementary_card_le G).mp hr E hE
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hkpos : 0 < k := by
    have := E.one_lt_card_iff_ne_bot.mpr hEne
    by_contra! hz
    have hk0 : k = 0 := by omega
    have hcardOne : Nat.card E = 1 := by simpa only [hk0,pow_zero] using hk
    omega
  have hk2 : k ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hk] using hE4
  interval_cases k
  · obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hk]; norm_num)
    have htG : orderOf (t : G) = 2 := (orderOf_coe t).trans ht
    have hEz : zpowers (t : G) = E := eq_of_le_of_card_ge
      (zpowers_le.mpr t.property) (by rw [Nat.card_zpowers,htG,hk]; norm_num)
    rw [← hEz,normalizer_zpowers_eq_centralizer_of_order_two _ htG]
    exact (hi t htG).trans (le_max_right _ _)
  · have hcard : Nat.card E = 4 := by simpa using hk
    have hAut : Nat.card (MulAut E) = 6 := by
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E 2 (by simpa using hcard)]
      norm_num [Fin.prod_univ_succ]
    have hker : primeRank p E.normalizerMonoidHom.ker =
        primeRank p (centralizer (E : Set G)) := by
      rw [normalizerMonoidHom_ker]
      exact primeRank_equiv p
        (subgroupOfEquivOfLe (centralizer_le_normalizer (E : Set G)))
    have h := primeRank_le_ker_add (p := p) E.normalizerMonoidHom
    rw [hker] at h
    exact (h.trans (Nat.add_le_add (hf E hE hcard)
      (odd_prime_rank_le_one_of_card_six hp hAut))).trans (le_max_left _ _)

end Theory.GroupTheory
