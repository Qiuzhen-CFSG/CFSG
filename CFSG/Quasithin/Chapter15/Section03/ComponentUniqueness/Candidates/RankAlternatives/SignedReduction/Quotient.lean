module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.OuterActor
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PrimePowerDecomposition
public import Mathlib.GroupTheory.Complement

/-!
# The prime-to-three quotient in the signed component reduction

For an ordinary component of positive three-rank, the normal three-prime
core centralizes the component. When the ambient odd core is trivial, its
intersection with the component is exactly the component two-core. Thus
its image in the prime-to-three quotient is the actual simple central
quotient; in particular it has trivial center.

An order-three outer actor remains outside that image and retains order
three. In an index-three residual extension its cyclic subgroup would be
a complement. Hence the nonsplit branch of A.3.18(2) forces theta(I) = L.
No identification of a split extension with a diagonal action is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18
(printed pp.51--52), and the reductions on pp.1135 and 1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction
variable {G : Type*} [Group G] [Finite G]

/-- A positive-three-rank component is centralized by the normal three-prime core. -/
theorem core_centralizes {L : Subgroup G} (hL : IsComponent G L)
    (hr : 1 ≤ primeRank 3 L) : pPrimeCore 3 G ≤ centralizer (L : Set G) := by
  rcases hL.normal_dichotomy (pPrimeCore 3 G) with hle | hc
  · have hcop : Nat.Coprime 3 (Nat.card L) := pPrimeCore_coprime_card.of_dvd_right
      (card_dvd_of_le hle)
    have hz : primeRank 3 L = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr
      (Nat.prime_three.coprime_iff_not_dvd.mp hcop)
    omega
  · rw [commutator_comm] at hc
    exact commutator_eq_bot_iff_le_centralizer.mp hc

/-- The quotient kernel on the component is precisely its two-core. -/
theorem core_comap {L : Subgroup G} (hL : IsComponent G L)
    (hodd : pPrimeCore 2 G = ⊥) (hr : 1 ≤ primeRank 3 L) :
    (pPrimeCore 3 G).comap L.subtype = pCore 2 L := by
  apply le_antisymm
  · intro x hx
    rw [← component_center_eq_twoCore hL hodd]
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (core_centralizes hL hr hx) y y.property)
  · have h23 : pCore 2 G ≤ pPrimeCore 3 G := by
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
      rw [hn]
      exact (show Nat.Coprime 3 2 by decide).pow_right n
    exact map_le_iff_le_comap.mp ((pCoreIn_le_of_subnormal 2 hL.1).trans h23)

/-- The actual component quotient maps isomorphically onto its image. -/
noncomputable def quotientEquiv {L : Subgroup G} (hL : IsComponent G L)
    (hodd : pPrimeCore 2 G = ⊥) (hr : 1 ≤ primeRank 3 L) :
    (L ⧸ pCore 2 L) ≃* L.map (QuotientGroup.mk' (pPrimeCore 3 G)) := by
  let f := (QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap L
  have hk : f.ker = pCore 2 L := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact core_comap hL hodd hr
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap_surjective L))

/-- The component image in the three-prime-core quotient is simple. -/
theorem image_simple {L : Subgroup G} (hL : IsComponent G L)
    (hodd : pPrimeCore 2 G = ⊥) (hr : 1 ≤ primeRank 3 L) :
    IsSimpleGroup (L.map (QuotientGroup.mk' (pPrimeCore 3 G))) := by
  let := hL.2
  let e := (QuotientGroup.quotientMulEquivOfEq (component_center_eq_twoCore hL hodd)).trans
    (quotientEquiv hL hodd hr)
  exact (MulEquiv.isSimpleGroup_congr e).mp IsQuasisimple.simple

/-- The component image has trivial center, including for a central two-cover. -/
theorem image_center {L : Subgroup G} (hL : IsComponent G L)
    (hodd : pPrimeCore 2 G = ⊥) (hr : 1 ≤ primeRank 3 L) :
    center (L.map (QuotientGroup.mk' (pPrimeCore 3 G))) = ⊥ := by
  let := hL.2
  let e := (QuotientGroup.quotientMulEquivOfEq (component_center_eq_twoCore hL hodd)).trans
    (quotientEquiv hL hodd hr)
  apply card_eq_one.mp
  rw [← Nat.card_congr (centerCongr e).toEquiv, Group.IsPerfect.center_quotient_center_eq_bot]
  exact Nat.card_unique

/-- An outside element of order three splits an index-three extension. -/
theorem complement_of_three_index {H : Subgroup G} (hi : H.index = 3)
    {x : G} (hx : orderOf x = 3) (hxH : x ∉ H) : H.IsComplement' (zpowers x) := by
  have hcard : Nat.card (zpowers x) = 3 := (Nat.card_zpowers x).trans hx
  let : Fact (Nat.Prime (Nat.card (zpowers x))) := ⟨hcard ▸ Nat.prime_three⟩
  have hb : H.subgroupOf (zpowers x) = ⊥ := by
    rcases (H.subgroupOf (zpowers x)).eq_bot_or_eq_top_of_prime_card with h | h
    · exact h
    · exact (hxH (subgroupOf_eq_top.mp h (mem_zpowers x))).elim
  apply isComplement'_of_card_mul_and_disjoint
  · rw [hcard, ← hi]
    exact H.card_mul_index
  · apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro a ha
    have hm : (⟨a, ha.2⟩ : zpowers x) ∈ H.subgroupOf (zpowers x) := ha.1
    rw [hb, mem_bot] at hm
    exact congrArg Subtype.val hm

/-- An actual outer conjugation cannot map into the component image. -/
theorem quotient_not_mem_of_outer {I L : Subgroup G}
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hr : 1 ≤ primeRank 3 L) {y : G} (hyI : y ∈ I)
    {α : MulAut L} (hconj : ConjugationOn L y α)
    (houter : α ∉ MulAut.innerSubgroup L) :
    QuotientGroup.mk' (pPrimeCore 3 I) ⟨y, hyI⟩ ∉
      (L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I)) := by
  let q := QuotientGroup.mk' (pPrimeCore 3 I)
  have hrK : 1 ≤ primeRank 3 (L.subgroupOf I) := by
    rwa [primeRank_equiv 3 (subgroupOfEquivOfLe hLI)]
  rintro ⟨l, hl, he⟩
  have hk : l⁻¹ * (⟨y, hyI⟩ : I) ∈ pPrimeCore 3 I := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (l⁻¹ * (⟨y, hyI⟩ : I)) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hc := core_centralizes hL hrK hk
  apply houter
  refine ⟨⟨l, hl⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (l : G) * (x : G) * (l : G)⁻¹ = (α x : G)
  rw [hconj x]
  have hcomm := congrArg Subtype.val
    (mem_centralizer_iff.mp hc (⟨x, hLI x.property⟩ : I) x.property)
  change (x : G) * ((l : G)⁻¹ * y) = ((l : G)⁻¹ * y) * (x : G) at hcomm
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right, mul_inv_cancel, mul_one] using
    congrArg (fun a : G => (l : G) * a * y⁻¹) hcomm

/-- Factoring out the three-prime core preserves an element of order three. -/
theorem quotient_order_three {I : Subgroup G} {y : G}
    (hyI : y ∈ I) (hy : orderOf y = 3) :
    orderOf (QuotientGroup.mk' (pPrimeCore 3 I) ⟨y, hyI⟩) = 3 := by
  have hi : orderOf (⟨y, hyI⟩ : I) = 3 := by simpa using hy
  have h := (QuotientGroup.mk' (pPrimeCore 3 I)).orderOf_eq_of_prime_power_of_coprime_ker
    (p := 3) (by rw [QuotientGroup.ker_mk']; exact pPrimeCore_coprime_card)
    (⟨y, hyI⟩ : I) ⟨1, by simpa only [pow_one, ← hi] using pow_orderOf_eq_one (⟨y, hyI⟩ : I)⟩
  exact h.trans hi

/-- The local rank bounds construct an outside order-three element in the quotient. -/
theorem exists_outside_quotient {Yplus M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hnot : ¬ Yplus ≤ L)
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2) :
    ∃ y ∈ Yplus, ∃ hyI : y ∈ I, orderOf y = 3 ∧
      orderOf (QuotientGroup.mk' (pPrimeCore 3 I) ⟨y, hyI⟩) = 3 ∧
      QuotientGroup.mk' (pPrimeCore 3 I) ⟨y, hyI⟩ ∉
        (L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I)) := by
  obtain ⟨y, hy, hy3, _, α, hα, hout⟩ := exists_order_three_outer_of_rank_two
    hθ hnot hLI hcomp hodd hrankL hrankI hindex
  have hyI : y ∈ I := by
    have hYI : Yplus ≤ I := hθ ▸ (theta_le (M ⊓ I)).trans inf_le_right
    exact hYI hy
  exact ⟨y, hy, hyI, hy3, quotient_order_three hyI hy3,
    quotient_not_mem_of_outer hLI hcomp (by omega) hyI hα hout⟩

/-- A nonsplit index-three residual extension contains no outside theta-generator. -/
theorem theta_le_of_nonsplit {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (hresindex : ((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))).relIndex
      (primeToResidual 3 (I ⧸ pPrimeCore 3 I)) = 3)
    (hnonsplit : ¬ ∃ D : Subgroup (primeToResidual 3 (I ⧸ pPrimeCore 3 I)),
      (((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))).subgroupOf
        (primeToResidual 3 (I ⧸ pPrimeCore 3 I))).IsComplement' D) :
    theta I ≤ L := by
  by_contra hn
  obtain ⟨y, _, hyI, _, hy3, hyL⟩ := exists_outside_quotient
    (Yplus := theta I) (M := I) (by rw [inf_idem]) hn hLI hcomp hodd hrankL hrankI hindex
  let qy := QuotientGroup.mk' (pPrimeCore 3 I) ⟨y, hyI⟩
  have hmem : qy ∈ primeToResidual 3 (I ⧸ pPrimeCore 3 I) :=
    mem_primeToResidual_of_pow (n := 1) (by simpa only [pow_one, ← hy3] using pow_orderOf_eq_one qy)
  let x : primeToResidual 3 (I ⧸ pPrimeCore 3 I) := ⟨qy, hmem⟩
  apply hnonsplit
  refine ⟨zpowers x, complement_of_three_index hresindex ?_ ?_⟩
  · simpa only [x, Subgroup.orderOf_mk] using hy3
  · exact hyL

/-- Transport the component center identity from the relative subgroup to L. -/
theorem local_center_eq_twoCore {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) : center L = pCore 2 L := by
  let e := subgroupOfEquivOfLe hLI
  have hK := component_center_eq_twoCore hcomp hodd
  apply le_antisymm
  · intro x hx
    have he : e.symm x ∈ center (L.subgroupOf I) :=
      ((centerCongr e).symm ⟨x, hx⟩).property
    rw [hK] at he
    rw [← pCore_map_iso 2 e]
    exact ⟨e.symm x, he, e.apply_symm_apply x⟩
  · intro x hx
    rw [← pCore_map_iso 2 e] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (centerCongr e ⟨y, hK.symm ▸ hy⟩).property

/-- The nonsplit alternative of A.3.18(2) yields the theta branch in the local reduction. -/
theorem theta_eq_of_nonsplit {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (hresindex : ((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))).relIndex
      (primeToResidual 3 (I ⧸ pPrimeCore 3 I)) = 3)
    (hnonsplit : ¬ ∃ D : Subgroup (primeToResidual 3 (I ⧸ pPrimeCore 3 I)),
      (((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))).subgroupOf
        (primeToResidual 3 (I ⧸ pPrimeCore 3 I))).IsComplement' D) :
    theta I = L := by
  let := hcomp.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLI)
  apply le_antisymm (theta_le_of_nonsplit hLI hcomp hodd hrankL hrankI hindex hresindex hnonsplit)
  rw [← theta_eq_self_of_quasisimple (local_center_eq_twoCore hLI hcomp hodd).le (by omega)]
  exact theta_mono hLI

/-- The component quotient equivalence uses the ambient quotient map on representatives. -/
theorem quotientEquiv_mk {L : Subgroup G} (hL : IsComponent G L)
    (hodd : pPrimeCore 2 G = ⊥) (hr : 1 ≤ primeRank 3 L) (x : L) :
    ((quotientEquiv hL hodd hr (QuotientGroup.mk' (pCore 2 L) x)) : G ⧸ pPrimeCore 3 G) =
      QuotientGroup.mk' (pPrimeCore 3 G) x := by
  rfl

/-- The component image cannot be one of the genuine central three-covers. -/
theorem no_center_three {L : Subgroup G} (hL : IsComponent G L)
    (hodd : pPrimeCore 2 G = ⊥) (hr : 1 ≤ primeRank 3 L) :
    ¬ Nonempty (center (L.map (QuotientGroup.mk' (pPrimeCore 3 G))) ≃*
      Multiplicative (ZMod 3)) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr e.toEquiv
  rw [image_center hL hodd hr] at hc
  norm_num [Nat.card_unique] at hc

/-- The ordinary residual branch of A.3.18(1) also gives the theta identity.
The reverse inclusion uses generation of the actual quasisimple component. -/
theorem theta_eq_of_threeResidual {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 1 ≤ primeRank 3 L)
    (hres : (primeToResidual 3 I).map I.subtype = L) : theta I = L := by
  let := hcomp.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLI)
  apply le_antisymm ((theta_le_threeResidual I).trans hres.le)
  rw [← theta_eq_self_of_quasisimple (local_center_eq_twoCore hLI hcomp hodd).le hrankL]
  exact theta_mono hLI

/-- The canonical quotient identification for an ambient subgroup L≤I.
This retains the relative component convention used in the chapter. -/
noncomputable def localQuotientEquiv {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 1 ≤ primeRank 3 L) :
    (L ⧸ pCore 2 L) ≃*
      (L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I)) := by
  let e := (subgroupOfEquivOfLe hLI).symm
  have hr : 1 ≤ primeRank 3 (L.subgroupOf I) := by
    rwa [primeRank_equiv 3 (subgroupOfEquivOfLe hLI)]
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (quotientEquiv hcomp hodd hr)

/-- The local identification is compatible with the quotient map on each element. -/
theorem localQuotientEquiv_mk {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 1 ≤ primeRank 3 L) (x : L) :
    (localQuotientEquiv hLI hcomp hodd hrankL (QuotientGroup.mk' (pCore 2 L) x) :
      I ⧸ pPrimeCore 3 I) =
      QuotientGroup.mk' (pPrimeCore 3 I) ⟨x, hLI x.property⟩ := by
  rfl

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction
