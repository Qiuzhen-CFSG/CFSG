module

public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.Quotient
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.PrimeToMonotone

/-!
# The local group in Lemma 16.4.5

Tight embedding places every involution centralizer C_G(i), for i in
K = C_G(L), inside H = N_G(L). Thus L is normal and quasisimple in that
centralizer. Condition (E1) makes its center a two-group. An elementary
abelian subgroup of order p² in L then shows that C_K(i) has order prime
to p: a centralizing element of order p would give rank at least three.
The normal p-prime core centralizes L by the component normal-subgroup
dichotomy, so it equals this actual relative centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Remark
16.3.3 and Lemma 16.4.5, pp.1178, 1184; A.3.18, pp.51–52, observation (*).
The exceptional model alternatives are not asserted here.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter16.Intersections
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem StandardSetup.involution_centralizer_le (h : StandardSetup T z L) {i : G}
    (hi : i ∈ centralizer (L : Set G)) (hi2 : orderOf i = 2) :
    involutionCentralizer i ≤ normalizer (L : Set G) := by
  have hp : IsPGroup 2 (zpowers i) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hi2, pow_one])
  have hne : zpowers i ≠ ⊥ := by
    intro he
    have hi1 : i = 1 := by simpa only [he, mem_bot] using mem_zpowers i
    simp [hi1] at hi2
  have hn := h.tight.normalizer_le hp hne (zpowers_le.mpr hi)
  rw [h.normalizers_eq, normalizer_zpowers_eq_centralizer_of_order_two i hi2] at hn
  exact hn

theorem StandardSetup.involution_component (h : StandardSetup T z L) {i : G}
    (hi : i ∈ centralizer (L : Set G)) (hi2 : orderOf i = 2) :
    IsCentralizerComponent i L := by
  have hLC : L ≤ involutionCentralizer i := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hi x hx)
  let : (L.subgroupOf (involutionCentralizer i)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLC).mpr (h.involution_centralizer_le hi hi2)
  let := h.component.quasisimple
  exact ⟨hLC, (inferInstance : (L.subgroupOf (involutionCentralizer i)).Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLC).symm⟩

private theorem quasisimple_primeToResidual_eq_top {p : ℕ} [Fact p.Prime] [IsQuasisimple G]
    (hZ : Nat.Coprime p (Nat.card (center G))) (hr : 1 ≤ primeRank p G) :
    primeToResidual p G = ⊤ := by
  rcases IsQuasisimple.normal_le_center_or_eq_top (primeToResidual p G) with hc | ht
  · have hd : p ∣ Nat.card G := by
      by_contra hn
      have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
      omega
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) p hd
    have hmem : x ∈ primeToResidual p G := mem_primeToResidual_of_pow (n := 1)
      (by simpa only [pow_one, ← hx] using pow_orderOf_eq_one x)
    have hdiv : p ∣ Nat.card (center G) := by
      have hd := orderOf_dvd_natCard (⟨x, hc hmem⟩ : center G)
      simpa only [Subgroup.orderOf_mk, hx] using hd
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hZ hdiv).elim
  · exact ht

private theorem centralizer_coprime_of_rank {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (L : Subgroup G) (hZ : Nat.Coprime p (Nat.card (center L)))
    (hrL : 2 ≤ primeRank p L) (hrG : primeRank p G ≤ 2) :
    Nat.Coprime p (Nat.card (centralizer (L : Set G))) := by
  classical
  let P : Sylow p L := Classical.choice inferInstance
  have hn : ¬ IsCyclic P := by
    intro hc
    have hh := P.primeRank_le_one_of_isCyclic hc
    omega
  obtain ⟨A, _, hAc, hA⟩ :=
    P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by rintro rfl; norm_num at hp) hn
  let := hA
  let E := (A.map (P : Subgroup L).subtype).map L.subtype
  let : IsElementaryAbelian p (A.map (P : Subgroup L).subtype) :=
    IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian p E := IsElementaryAbelian.map_subtype
  have hEc : Nat.card E = p ^ 2 := by
    simpa only [E, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective (P : Subgroup L).subtype_injective] using hAc
  have hEL : E ≤ L := map_subtype_le _
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) p hd
  have hxG : orderOf (x : G) = p := (orderOf_coe x).trans hx
  have hxL : (x : G) ∉ L := by
    intro hxL
    have hz : (⟨x, hxL⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (mem_centralizer_iff.mp x.property l l.property)
    have hd := orderOf_dvd_natCard (⟨⟨x, hxL⟩, hz⟩ : center L)
    simp only [Subgroup.orderOf_mk, hxG] at hd
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hZ hd
  have hfix : E ≤ centralizer ({(x : G)} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp x.property e (hEL he))
  have hb := IsElementaryAbelian.primeRank_ge_of_fixed_join E x hxG
    (fun he => hxL (hEL he)) hfix hEc
  omega


/-- The local component's center has order prime to every odd prime. -/
theorem StandardSetup.component_center_coprime
    {κ : GroupClass} (hG : Hypothesis1611 κ G) (h : StandardSetup T z L)
    {p : ℕ} (hp : Odd p) : Nat.Coprime p (Nat.card (center L)) := by
  rw [hG.evenType.component_center_eq_twoCore h.involution h.component]
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  rw [hn]
  exact hp.coprime_two_right.pow_right n

/-- Positive odd-prime rank makes the quasisimple component its own
prime-to-p residual. This is intrinsic generation, not an assumed ambient
residual conclusion. -/
theorem StandardSetup.component_primeToResidual_eq_top
    {κ : GroupClass} (hG : Hypothesis1611 κ G) (h : StandardSetup T z L)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : 1 ≤ primeRank p L) :
    primeToResidual p L = ⊤ := by
  let := h.component.quasisimple
  exact quasisimple_primeToResidual_eq_top (h.component_center_coprime hG hp) hr

/-- The centralizer of L inside C_G(i) has order prime to p. -/
theorem StandardSetup.local_centralizer_coprime
    {κ : GroupClass} (hG : Hypothesis1611 κ G) (h : StandardSetup T z L)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : 1 < primeRank p L)
    {i : G} (hi : i ∈ centralizer (L : Set G)) (hi2 : orderOf i = 2) :
    Nat.Coprime p (Nat.card (centralizer
      (L.subgroupOf (involutionCentralizer i) : Set (involutionCentralizer i)))) := by
  have hL := h.involution_component hi hi2
  have he := subgroupOfEquivOfLe hL.1
  apply centralizer_coprime_of_rank hp
  · rw [Nat.card_congr (centerCongr he).toEquiv]
    exact h.component_center_coprime hG hp
  · rw [primeRank_equiv p he]
    exact hr
  · exact (hG.involution_centralizer_sqtk hi2).stronglyQuasithin p Fact.out hp

/-- The p-prime core of the involution centralizer is exactly its
centralizer of the component. In particular this identifies the kernel
needed to compare A.3.18 with the fixed star quotient. -/
theorem StandardSetup.local_primeCore_eq_centralizer
    {κ : GroupClass} (hG : Hypothesis1611 κ G) (h : StandardSetup T z L)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : 1 < primeRank p L)
    {i : G} (hi : i ∈ centralizer (L : Set G)) (hi2 : orderOf i = 2) :
    pPrimeCore p (involutionCentralizer i) =
      centralizer (L.subgroupOf (involutionCentralizer i) :
        Set (involutionCentralizer i)) := by
  have hL := h.involution_component hi hi2
  let J := L.subgroupOf (involutionCentralizer i)
  let : J.Normal := (normal_subgroupOf_iff_le_normalizer hL.1).mpr
    (h.involution_centralizer_le hi hi2)
  apply le_antisymm
  · rcases hL.2.normal_dichotomy (pPrimeCore p (involutionCentralizer i)) with hle | hc
    · have hcop : Nat.Coprime p (Nat.card J) := pPrimeCore_coprime_card.of_dvd_right
        (card_dvd_of_le hle)
      have hz : primeRank p J = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop)
      rw [primeRank_equiv p (subgroupOfEquivOfLe hL.1)] at hz
      omega
    · rw [commutator_comm] at hc
      exact commutator_eq_bot_iff_le_centralizer.mp hc
  · apply le_sSup
    exact ⟨inferInstance, h.local_centralizer_coprime hG hp hr hi hi2⟩

end CFSG.Quasithin.Chapter16.Intersections
