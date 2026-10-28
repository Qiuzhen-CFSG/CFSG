module
public import CFSG.Quasithin.Chapter3.Section01.SourceE213ActionTransfer
public import Theory.Representation.BinaryOffender.ConjugateSpan
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.SmallExclusion
/-!
# The odd linear outside-core branch for the original qrc module

In the non-FF case, V lies in O₂(H∩M), and every (H∩M)-conjugate lies in
O₂(H∩M)≤T≤M₀. The original conjugation offender theorem makes their span
an elementary group. Its image in H/J is therefore normal elementary in
the actual maximal subgroup. The proved odd PSL₃ normal-elementary bound
makes the image of the original V have order at most two, including p=3.
Outside O₂(H), that image is nontrivial; its dihedral pair gives the cubic
bound on the original M₀ action.

This is a specialized source route, using the actual non-FF qrc action and
its core placement. It does not assert the unrestricted odd PSL₃ local
cyclicity shortcut in printed E.2.7, which fails at characteristic three.
Source: Aschbacher--Smith D.1.2(1), E.2.7--13, and 3.1.6(i), printed
pp.172,219--225,573--574.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The actual non-FF module has elementary span under H∩M. -/
theorem QrcHypotheses.intersection_span_elementary
    (h : QrcHypotheses T M M₀ H V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hnf : letI := h.module_elementary
      ¬ IsFFModule (imageRepresentation M₀ V h.module_normalized)) :
    IsElementaryAbelian 2 (conjugateSpanBy V (H ⊓ M)) := by
  let := h.module_elementary
  let B := H ⊓ M
  have hTB : (T : Subgroup G) ≤ B :=
    le_inf h.right_mem.1.1.2 (h.sylow_le.trans h.left_le)
  have hcT : B.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hc := pCore_isPGroup.le_sylow_of_normal (T.subtype hTB)
    have hm := map_mono (f := B.subtype) hc
    change (pCore 2 B).map B.subtype ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTB] using hm
  let f := actionHom M₀ V h.module_normalized
  apply conjugateSpan_elementary_of_notFF M₀ B V f.rangeRestrict
    (imageRepresentation M₀ V h.module_normalized)
    (by rw [MonoidHom.ker_rangeRestrict,actionHom_ker]) (fun _ _ => rfl) ?_ hnf
  intro g hg
  have he : (B.pCoreIn 2).map (MulAut.conj g).toMonoidHom = B.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (twoCore_normalized B hg)
  exact ((map_mono (h.module_le_intersection_core hG hM)).trans_eq he).trans
    (hcT.trans h.sylow_le)

/-- The non-FF original module has order-two image in the odd linear source row. -/
theorem QrcHypotheses.odd_linear_image_card_le_two
    (h : QrcHypotheses T M M₀ H V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hnf : letI := h.module_elementary
      ¬ IsFFModule (imageRepresentation M₀ V h.module_normalized))
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) = ⊤)
    {p : ℕ} (hpprime : p.Prime) (hpodd : Odd p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
        (T.subtype h.right_mem.1.1.2) hp))) 3 p) :
    Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
      (T.subtype h.right_mem.1.1.2) hp))) ≤ 2 := by
  let := h.module_elementary
  let S := T.subtype h.right_mem.1.1.2
  let B := ChapterB.minimalParabolicMax S hp
  let J := ChapterB.minimalParabolicCore S hp
  let q := QuotientGroup.mk' J
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := K.map q
  let A₀ := conjugateSpanBy V (H ⊓ M)
  have hVB : V ≤ H ⊓ M := (h.module_le_intersection_core hG hM).trans (pCoreIn_le _ _)
  have hA₀B : A₀ ≤ H ⊓ M := conjugateSpanBy_le_self hVB
  have hA₀H : A₀ ≤ H := hA₀B.trans inf_le_left
  let A := A₀.subgroupOf H
  let : IsElementaryAbelian 2 A₀ := h.intersection_span_elementary hG hM hnf
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hA₀H
  let Aq := A.map q
  let : IsElementaryAbelian 2 Aq := IsElementaryAbelian.map q
  have hAB : A ≤ B := by
    change A ≤ ChapterB.minimalParabolicMax (T.subtype h.right_mem.1.1.2) hp
    rw [h.intrinsic_maximal_eq_intersection hp]
    exact subgroupOf_mono H hA₀B
  have hBA : B ≤ normalizer (A : Set H) := by
    change ChapterB.minimalParabolicMax (T.subtype h.right_mem.1.1.2) hp ≤
      normalizer (A₀.subgroupOf H : Set H)
    rw [h.intrinsic_maximal_eq_intersection hp, ←subgroupOf_normalizer_eq hA₀H]
    exact subgroupOf_mono H (le_normalizer_conjugateSpanBy V (H ⊓ M))
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact hK.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective K.subtype_injective)
  have hi := ChapterE.Structure.source_normal_simple_image S hp hs K hK hgen
  let : D.Normal := hi.2.2.1
  let : IsSimpleGroup D := hi.1
  let hpq := (ChapterE.Structure.source_star_minimal_core_free S hp).1
  have hO : pCore 2 (H ⧸ J) = ⊥ := bot_unique
    ((ChapterB.minimalParabolicTwoCore_le_core Sq hpq).trans
      (ChapterE.Structure.source_star_minimal_core_free S hp).2.le)
  have hBq : B.map q = ChapterB.minimalParabolicMax Sq hpq :=
    ChapterB.minimalParabolicMax_map_core S hp q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])
  have hAqB : Aq ≤ ChapterB.minimalParabolicMax Sq hpq := hBq ▸ map_mono hAB
  have hBqA : ChapterB.minimalParabolicMax Sq hpq ≤ normalizer (Aq : Set (H ⧸ J)) := by
    rw [←hBq]
    exact (map_mono hBA).trans (le_normalizer_map q)
  have hc : Nat.card Aq ≤ 2 := ChapterE.Structure.OddDegreeThree.linear_normal_elementary_card_le_two
    Sq hpq D hi.2.2.2 hO hpprime hpodd hm Aq hAqB hBqA
  have hVA : V.subgroupOf H ≤ A := subgroupOf_mono H (le_conjugateSpanBy V (H ⊓ M))
  exact (card_le_of_le (map_mono (f := q) hVA)).trans hc

end CFSG.Quasithin.Chapter3

namespace CFSG.Quasithin.Chapter3
open Subgroup Theory.GroupTheory Representation.BinaryOffender ChapterD ChapterD.UniqueFactor
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The original odd PSL₃ branch, including prime three, has cubic ratio at most two. -/
theorem QrcHypotheses.odd_linear_cubicRatio_le_two
    (h : QrcHypotheses T M M₀ H V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hout : ¬ V ≤ H.pCoreIn 2)
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) = ⊤)
    {p : ℕ} (hpprime : p.Prime) (hpodd : Odd p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
        (T.subtype h.right_mem.1.1.2) hp))) 3 p) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 := by
  let := h.module_elementary
  by_cases hff : IsFFModule (imageRepresentation M₀ V h.module_normalized)
  · exact ((isFFModule_iff_cubicRatio_le_one _).mp hff).trans (by norm_num)
  let S := T.subtype h.right_mem.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := h.module_le_sylow.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => h.module_le_sylow hx
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) := h.intrinsic_module_normalized
  have hvn : (W.subgroupOf (S : Subgroup H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr hTV
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hp).pCoreIn 2 :=
    h.intrinsic_module_le_maximal_core hG hM hp
  have hWout : ¬ W ≤ ChapterB.minimalParabolicCore S hp := by
    intro he
    have hc : W ≤ pCore 2 H := by
      rw [← ChapterB.minimalParabolic_sylow_inf_core S hp]
      exact le_inf hWS he
    apply hout
    have hm := map_mono (f := H.subtype) hc
    change (V.subgroupOf H).map H.subtype ≤ H.pCoreIn 2 at hm
    simpa only [map_subgroupOf_eq_of_le hVH] using hm
  let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
  have hcard : Nat.card (W.map q) = 2 := by
    have hc := h.odd_linear_image_card_le_two hG hM hff hp K hK hgen hpprime hpodd hm
    have hne : W.map q ≠ ⊥ := by
      intro he
      exact hWout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff W).mp he)
    have hpos := (one_lt_card_iff_ne_bot _).mpr hne
    change Nat.card (W.map q) ≤ 2 at hc
    omega
  obtain ⟨w⟩ := ChapterE.Witnesses.Involution.source_star_order_two S hp W hWS hvn hWcore hcard
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp
        (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) h.right_mem.1.1))
  exact h.cubicRatio_le_nat_of_intrinsic_action 2
    (ChapterE.Witnesses.BenderPlacement.original_witness_cubicRatio_le_two
      hp hWS hvn hWcore hWout hfit
      (ChapterE.Witnesses.BenderPlacement.OriginalWitness.of_dihedral (n := 1) w) le_rfl hTV)
end CFSG.Quasithin.Chapter3
