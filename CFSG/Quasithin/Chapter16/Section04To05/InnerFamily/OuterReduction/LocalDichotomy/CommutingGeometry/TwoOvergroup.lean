module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.ProductIdentification

/-!
# The invariant two-overgroup for the order-four construction

The commuting pair lies in a Sylow subgroup of K′⟨s⟩. Intersecting that
Sylow with its normal subgroup K′ gives an s-invariant Sylow of K′ which
contains r. The strict inequality ⟨z⟩ < T_C shows that it has order greater
than two. The checked (+) theorem and Sylow maximality identify its full
s-centralizer with ⟨r⟩. The other involution s lies outside it.

These are the inputs to the remaining order-four and D₈ construction; this
module does not assume or assert those geometric witnesses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.9(2), printed p.1190, the paragraph after (+).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.CommutingGeometry
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_inf_normal {P H K : Subgroup G} (hP : SylowIn P H)
    (hKH : K ≤ H) (hNK : H ≤ normalizer (K : Set G)) : SylowIn (P ⊓ K) K := by
  obtain ⟨S, rfl⟩ := hP
  let : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hNK
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal (K.subgroupOf H)
  let e := subgroupOfEquivOfLe hKH
  refine ⟨U.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((U : Subgroup _).map e.toMonoidHom).map K.subtype = _
  rw [hU]
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨⟨w.val, hw, rfl⟩, w.property⟩
  · rintro ⟨⟨w, hw, rfl⟩, hk⟩
    exact ⟨⟨w, hk⟩, ⟨⟨w, hk⟩, hw, rfl⟩, rfl⟩

/-- Construct an invariant Sylow two-subgroup containing the marked involution,
with its centralizer fixed exactly by (+). -/
theorem exists_invariant_two_subgroup
    (K S : Subgroup G) (hS : SylowIn S K) (hlarge : 2 < Nat.card S)
    {r s : G} (hrK : r ∈ K) (hr2 : orderOf r = 2) (hs2 : orderOf s = 2)
    (hcomm : Commute r s) (hsN : s ∈ normalizer (K : Set G))
    (hfixed : SylowIn (zpowers r) (K ⊓ centralizer ({s} : Set G))) :
    ∃ Q : Subgroup G, Q ≤ K ∧ IsPGroup 2 Q ∧ 2 < Nat.card Q ∧ r ∈ Q ∧
      s ∈ normalizer (Q : Set G) ∧ Q ⊓ centralizer ({s} : Set G) = zpowers r := by
  let H := K ⊔ zpowers s
  let V := zpowers r ⊔ zpowers s
  have hp (x : G) (hx : orderOf x = 2) : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hsr : s ∈ normalizer (zpowers r : Set G) :=
    (centralizer_le_normalizer _) (by
      rw [zpowers_eq_closure, centralizer_closure]
      exact mem_centralizer_singleton_iff.mpr hcomm.eq.symm)
  have hV : IsPGroup 2 V := (hp r hr2).to_sup_of_normal_left' (hp s hs2) (zpowers_le.mpr hsr)
  have hVH : V ≤ H := sup_le_sup (zpowers_le.mpr hrK) le_rfl
  obtain ⟨P, hP⟩ := (hV.of_equiv (subgroupOfEquivOfLe hVH).symm).exists_le_sylow
  let P' : Subgroup G := (P : Subgroup H).map H.subtype
  have hP'H : SylowIn P' H := ⟨P, rfl⟩
  have hVP : V ≤ P' := by
    rw [← map_subgroupOf_eq_of_le hVH]
    exact map_mono hP
  have hHN : H ≤ normalizer (K : Set G) := sup_le K.le_normalizer (zpowers_le.mpr hsN)
  have hQ : SylowIn (P' ⊓ K) K := sylow_inf_normal hP'H le_sup_left hHN
  have hc : Nat.card (P' ⊓ K : Subgroup G) = Nat.card S := by
    obtain ⟨x, _, he⟩ := hQ.exists_conjugator hS
    rw [← he]
    exact (card_map_of_injective (MulAut.conj x).injective).symm
  have hrQ : r ∈ P' ⊓ K := ⟨hVP (mem_sup_left (mem_zpowers r)), hrK⟩
  have hsP : s ∈ P' := hVP (mem_sup_right (mem_zpowers s))
  have hQN : s ∈ normalizer ((P' ⊓ K : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨P'.le_normalizer hsP, hsN⟩
  refine ⟨P' ⊓ K, inf_le_right, hQ.isPGroup, hc ▸ hlarge, hrQ, hQN, ?_⟩
  apply hfixed.maximal
  · exact hQ.isPGroup.to_le inf_le_left
  · exact inf_le_inf_right _ inf_le_right
  · exact zpowers_le.mpr ⟨hrQ, mem_centralizer_singleton_iff.mpr hcomm.eq⟩

/-- The other marked involution lies outside this two-overgroup. -/
theorem not_mem_of_fixed_line {Q : Subgroup G} {r s : G}
    (hr2 : orderOf r = 2) (hs2 : orderOf s = 2)
    (hne : s ≠ r) (hfixed : Q ⊓ centralizer ({s} : Set G) = zpowers r) : s ∉ Q := by
  intro hsQ
  have hsR : s ∈ zpowers r := hfixed ▸ ⟨hsQ, mem_centralizer_singleton_iff.mpr rfl⟩
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hr2] at hsR
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hsR
  have hn2 : n < 2 := Finset.mem_range.mp hn
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · have hs1 : s = 1 := by simpa only [pow_zero] using he.symm
    simp [hs1] at hs2
  · exact hne (by simpa only [pow_one] using he.symm)

/-- The source's strict T_C inequality supplies the large invariant
Sylow subgroup of K′ needed by the order-four construction. -/
theorem exists_invariant_two_subgroup_of_setup
    {T : Sylow 2 G} {z g r l : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hl : l ∈ L) (hcomm : Commute r (MulAut.conj l r))
    (hne : MulAut.conj l r ≠ r) (hlarge : zpowers z < commutingSylow T L) :
    ∃ Q : Subgroup G, Q ≤ (centralizer (L : Set G)).conjBy g ∧
      IsPGroup 2 Q ∧ 2 < Nat.card Q ∧ r ∈ Q ∧
      MulAut.conj l r ∈ normalizer (Q : Set G) ∧
      Q ⊓ centralizer ({MulAut.conj l r} : Set G) = zpowers r := by
  have hc : 2 < Nat.card (commutingSylow T L) := by
    by_contra hn
    have he : zpowers z = commutingSylow T L :=
      eq_of_le_of_card_ge hlarge.le (by rw [Nat.card_zpowers, h.involution]; omega)
    exact hlarge.ne he
  have hS := (commutingSylow_sylow h.toStandardSetup).map (MulAut.conj g)
  have hc' : 2 < Nat.card ((commutingSylow T L).conjBy g) := by
    change 2 < Nat.card ((commutingSylow T L).map (MulAut.conj g).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hc
  obtain ⟨hsN, hfix⟩ := h.commuting_conjugate_sylow_centralizer hsmall hempty hr hr2 hl hcomm hne
  exact exists_invariant_two_subgroup _ _ hS hc' (h.sylow.le hr).1 hr2
    (((MulAut.conj l).orderOf_eq r).trans hr2) hcomm hsN hfix

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.CommutingGeometry
