module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Solvability
public import Theory.Quasithin.Rank

/-!
# The local deduction in the Suzuki exclusion

The invariant characteristic-two Borel lies in M ∩ I by 15.3.33(1).
Its maximality among S-invariant proper subgroups of L₀ = ⟨L^S⟩ then
identifies it with (M ∩ I) ∩ L₀. Mutual normalization of Y₊ and this Borel
implies [Y₊, B] ≤ O₂(B): their intersection is a three-free subgroup of
a two-by-three group, hence is a normal two-subgroup of B.

An explicit order-three Borel detector and Y₊ = θ(M ∩ I) then give the
contradiction. The detector and Borel construction remain hypotheses of
this reduction. In particular this module does not assert 15.3.34.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.11(4)--(6), 15.3.33(1), and 15.3.34, printed pp.1123 and 1134.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A three-free subgroup of a two-by-three group lies in its two-core. -/
theorem le_twoCore_of_three_free {Y H : Subgroup G} (hHY : H ≤ Y)
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y)) (hH : ¬ 3 ∣ Nat.card H) :
    H ≤ Y.pCoreIn 2 := by
  let D := H.subgroupOf Y
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hp : IsPGroup 3 (D.map q) := hY.to_subgroup _
  have hc : Nat.card (D.map q) = 1 := hp.card_eq_or_dvd.resolve_right (by
    intro hd
    apply hH
    have he : Nat.card D = Nat.card H := Nat.card_congr (subgroupOfEquivOfLe hHY).toEquiv
    rw [← he]
    exact hd.trans (D.card_map_dvd q))
  have hb : D.map q = ⊥ := Subgroup.card_eq_one.mp hc
  have hD : D ≤ pCore 2 Y := by
    simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hb
  simpa only [D, Subgroup.map_subgroupOf_eq_of_le hHY, pCoreIn] using
    (Subgroup.map_mono (f := Y.subtype) hD)

omit [Finite G] in
/-- Mutual normalization only gives a trivial action on the Borel two-core quotient. -/
theorem commutator_le_borel_twoCore {Y B : Subgroup G}
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y)) (hB : ¬ 3 ∣ Nat.card B)
    (hYB : Y ≤ normalizer (B : Set G))
    (hBY : B ≤ normalizer (Y : Set G)) : ⁅Y, B⁆ ≤ B.pCoreIn 2 := by
  have hI : Y ⊓ B ≤ Y.pCoreIn 2 := le_twoCore_of_three_free inf_le_left hY
    (fun hd => hB (hd.trans (card_dvd_of_le inf_le_right)))
  have hp : IsPGroup 2 (Y ⊓ B : Subgroup G) := (isPGroup_pCoreIn 2 Y).to_le hI
  have hn : B ≤ normalizer ((Y ⊓ B : Subgroup G) : Set G) :=
    le_normalizer_inf hBY B.le_normalizer
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hBY)
    (le_normalizer_iff_commutator_le_right.mp hYB)).trans
      (le_pCoreIn_of_normalizes hp inf_le_right hn)

/-- The maximal invariant Borel is the actual intersection with M. -/
theorem borel_eq_intersection
    {Yplus S M I L B : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hLI : L ≤ I) (hLM : ¬ L ≤ M)
    (hBL : B ≤ localSpan L S)
    (hBN : Yplus ⊔ S ≤ normalizer (B : Set G))
    (hBF : generalizedFitting B = pCore 2 B)
    (hmax : ∀ D : Subgroup G, B ≤ D → D ≤ localSpan L S →
      S ≤ normalizer (D : Set G) → D = B ∨ D = localSpan L S) :
    B = (M ⊓ I) ⊓ localSpan L S := by
  have hSI : S ≤ I := le_sup_right.trans hI.1.2
  have hL0I : localSpan L S ≤ I := conjugateSpanBy_le hLI
    (hSI.trans I.le_normalizer)
  have hBMI := lemma_15_3_33_1_of_threeGroup_quotient hI hSylow h25 hodd
    hSM hMI hY (hBL.trans hL0I) hBN hBF
  have hSN : S ≤ normalizer (((M ⊓ I) ⊓ localSpan L S : Subgroup G) : Set G) :=
    le_normalizer_inf (le_normalizer_inf (hSM.trans M.le_normalizer)
      (hSI.trans I.le_normalizer)) (le_normalizer_conjugateSpanBy L S)
  rcases hmax _ (le_inf hBMI hBL) inf_le_right hSN with he | he
  · exact he.symm
  · exfalso
    apply hLM
    exact (le_conjugateSpanBy L S).trans (he.symm.le.trans (inf_le_left.trans inf_le_left))

/-- The local contradiction once the Borel order-three action kernel has been computed.
The detector is an explicit unfinished model obligation, not a source conclusion. -/
theorem false_of_borel_detection
    {Yplus S M I L B : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (htheta : Yplus = theta (M ⊓ I))
    (hLI : L ≤ I) (hLM : ¬ L ≤ M)
    (hBL : B ≤ localSpan L S)
    (hBN : Yplus ⊔ S ≤ normalizer (B : Set G))
    (hBF : generalizedFitting B = pCore 2 B)
    (hmax : ∀ D : Subgroup G, B ≤ D → D ≤ localSpan L S →
      S ≤ normalizer (D : Set G) → D = B ∨ D = localSpan L S)
    (hthree : ¬ 3 ∣ Nat.card B)
    (hdetect : ∀ y ∈ Yplus, orderOf y = 3 →
      (∀ b ∈ B, ⁅y, b⁆ ∈ B.pCoreIn 2) →
      y ∈ centralizer (localSpan L S : Set G)) : False := by
  have he := borel_eq_intersection hI hSylow h25 hodd hSM hMI hY hLI hLM
    hBL hBN hBF hmax
  have hBY : B ≤ normalizer (Yplus : Set G) := by
    rw [he]
    exact inf_le_left.trans (hMI.symm.le.trans inf_le_right)
  have hc := commutator_le_borel_twoCore hY hthree
    (le_sup_left.trans hBN) hBY
  have hYC : Yplus ≤ centralizer (localSpan L S : Set G) := by
    rw [htheta, theta, Subgroup.closure_le]
    intro y hy
    have hyY : y ∈ Yplus := htheta.symm ▸ Subgroup.subset_closure hy
    exact hdetect y hyY hy.2 (fun b hb => hc (commutator_mem_commutator hyY hb))
  have hLC : L ≤ centralizer (Yplus : Set G) :=
    (le_conjugateSpanBy L S).trans (le_centralizer_iff.mp hYC)
  apply hLM
  have hLN : L ≤ I ⊓ normalizer (Yplus : Set G) :=
    le_inf hLI (hLC.trans (Subgroup.centralizer_le_normalizer _))
  rw [hMI] at hLN
  exact hLN.trans inf_le_left

/-- Cauchy's theorem supplies a nontrivial cyclic three-subgroup. -/
theorem positive_three_rank_of_dvd_card (hd : 3 ∣ Nat.card G) : 1 ≤ primeRank 3 G := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using hx)
  have hn : Nontrivial (zpowers x) := (Subgroup.nontrivial_iff_ne_bot _).mpr (by
    intro hb
    have hxe : x = 1 := Subgroup.mem_bot.mp (hb ▸ mem_zpowers x)
    simp [hxe] at hx)
  let := hn
  exact (Group.rank_pos (zpowers x)).trans_le
    (le_csSup (primeRank_bddAbove 3 G) ⟨zpowers x, hp, inferInstance, inferInstance, le_rfl⟩)
end CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion
