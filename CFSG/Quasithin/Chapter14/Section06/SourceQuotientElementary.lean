module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuotientRank
public import Theory.ElementaryAbelian.PrimeRankCard
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd

/-!
# The original normal elementary image in the two-core quotient

The abelian span U_H contains the suitable involution and therefore lies
in the actual Sylow intersection T ∩ I. Its H-normality makes its image
normal in the quotient Sylow. The index comparison of 14.6.8 computes the
rank of this literal image, supplying the rank-four normal elementary
subgroup used in the last contradiction of 14.6.9. The minimal-parabolic
core meets this Sylow in O₂(I), so the literal image in the star quotient
has the same order and the same rank. This transfer does not require the
two cores to be equal.

Source: Aschbacher--Smith, 14.6.8--9, printed pp.1024--1028.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original span lies in the prescribed Sylow intersection and is normal
there; the ambient containment uses the chosen suitable element in the span. -/
theorem source_span_sylow_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I) :
    let U := (conjugateSpanBy (localModule T M) H).subgroupOf I
    IsElementaryAbelian 2 U ∧ U ≤ (S : Subgroup I) ∧
      (U.subgroupOf (S : Subgroup I)).Normal ∧
      conjugateSpanBy (localModule T M) H ≤ I := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let : IsElementaryAbelian 2 D.UH := h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy D.V D.H).trans h.UH_le_QH)
  have hUT : D.UH ≤ (T : Subgroup G) := h.UH_le_QH.trans h.QH_le_T
  have hUI : D.UH ≤ I := by
    intro v hv
    apply hI.1.2.1
    refine ⟨hUT hv,?_⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg D.UH.subtype (mul_comm (⟨v,hv⟩ : D.UH) ⟨u,hu⟩))
  let U := D.UH.subgroupOf I
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUI
  have hUS : U ≤ (S : Subgroup I) := by
    have he : ((T : Subgroup G) ⊓ I).subgroupOf I = (S : Subgroup I) := by
      rw [←hS]
      exact comap_map_eq_self_of_injective I.subtype_injective _
    rw [←he]
    exact comap_mono (le_inf hUT hUI)
  have hSU : (S : Subgroup I) ≤ normalizer (U : Set I) := by
    rw [←subgroupOf_normalizer_eq hUI]
    intro s hs
    have hsT : (s : G) ∈ T := (hS ▸ mem_map_of_mem I.subtype hs).1
    exact (le_normalizer_conjugateSpanBy _ _) (hH.1.2 hsT)
  exact ⟨(inferInstance : IsElementaryAbelian 2 U),hUS,
    (normal_subgroupOf_iff_le_normalizer hUS).mpr hSU,hUI⟩

/-- The original span yields a normal elementary subgroup of rank at least
four in the prescribed Sylow of I/O₂(I). -/
theorem source_twoCore_quotient_elementary_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (hF : generalizedFitting I ≠ pCore 2 I)
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let U := (conjugateSpanBy (localModule T M) H).subgroupOf I
    let Sq := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
    IsElementaryAbelian 2 (U.map q) ∧ U.map q ≤ (Sq : Subgroup (I ⧸ pCore 2 I)) ∧
      ((U.map q).subgroupOf (Sq : Subgroup (I ⧸ pCore 2 I))).Normal ∧
      4 ≤ primeRank 2 (U.map q) := by
  let U := (conjugateSpanBy (localModule T M) H).subgroupOf I
  obtain ⟨hUE,hUS,hUN,hUI⟩ := source_span_sylow_normal hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI S hS
  let : IsElementaryAbelian 2 U := hUE
  let q := QuotientGroup.mk' (pCore 2 I)
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
  let W := U.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hSU : (S : Subgroup I) ≤ normalizer (U : Set I) :=
    (normal_subgroupOf_iff_le_normalizer hUS).mp hUN
  have hWS : W ≤ (Sq : Subgroup (I ⧸ pCore 2 I)) := map_mono hUS
  have hWN : (W.subgroupOf (Sq : Subgroup (I ⧸ pCore 2 I))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr
      ((map_mono hSU).trans (le_normalizer_map q))
  refine ⟨(inferInstance : IsElementaryAbelian 2 W),hWS,hWN,?_⟩
  change 4 ≤ primeRank 2 W
  have hbound := (source_lemma_14_6_8 hG T hempty hM hunique hmany hcard e
    hab H hH u hu I hI S hS hF).2
  have hfour : 4 ≤ Nat.log 2 ((I.pCoreIn 2).relIndex
      (conjugateSpanBy (localModule T M) H)) := hrank.trans hbound
  have hcore : (I.pCoreIn 2).subgroupOf I = pCore 2 I :=
    comap_map_eq_self_of_injective I.subtype_injective _
  have hsize : Nat.card W = (I.pCoreIn 2).relIndex (conjugateSpanBy (localModule T M) H) := by
    rw [←relIndex_subgroupOf hUI,hcore]
    simpa only [U,W,q,QuotientGroup.ker_mk'] using (relIndex_ker U q).symm
  rw [←IsElementaryAbelian.log_card_eq_primeRank (p := 2) W,hsize]
  exact hfour

/-- The same rank-four normal elementary subgroup in the literal parabolic
core quotient. The Sylow intersection of the two kernels is equal by B.6.8. -/
theorem source_parabolic_quotient_elementary_rank_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (hF : generalizedFitting I ≠ pCore 2 I)
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) :
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP)
    let U := (conjugateSpanBy (localModule T M) H).subgroupOf I
    let Sq := S.mapSurjective
      (QuotientGroup.mk'_surjective (ChapterB.minimalParabolicCore S hP))
    IsElementaryAbelian 2 (U.map q) ∧ U.map q ≤ (Sq : Subgroup _) ∧
      ((U.map q).subgroupOf (Sq : Subgroup _)).Normal ∧
      4 ≤ primeRank 2 (U.map q) := by
  let U := (conjugateSpanBy (localModule T M) H).subgroupOf I
  obtain ⟨hUE,hUS,hUN,_⟩ := source_span_sylow_normal hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI S hS
  let : IsElementaryAbelian 2 U := hUE
  let J := ChapterB.minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := U.map q
  let W₂ := U.map (QuotientGroup.mk' (pCore 2 I))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 W₂ := IsElementaryAbelian.map _
  have hWS : W ≤ (Sq : Subgroup _) := map_mono hUS
  have hWN : (W.subgroupOf (Sq : Subgroup _)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr
      ((map_mono ((normal_subgroupOf_iff_le_normalizer hUS).mp hUN)).trans
        (le_normalizer_map q))
  refine ⟨(inferInstance : IsElementaryAbelian 2 W),hWS,hWN,?_⟩
  change 4 ≤ primeRank 2 W
  have hker : J.subgroupOf U = (pCore 2 I).subgroupOf U := by
    rw [←ChapterB.minimalParabolic_sylow_inf_core S hP]
    ext x
    exact (and_iff_right (hUS x.property)).symm
  have hsize : Nat.card W = Nat.card W₂ := by
    rw [←relIndex_ker,←relIndex_ker]
    simp only [q,QuotientGroup.ker_mk',relIndex,hker]
  have hfour := (source_twoCore_quotient_elementary_rank hG T hempty hM hunique
    hmany hcard e hab H hH u hu I hI S hS hF hrank).2.2.2
  rw [←IsElementaryAbelian.log_card_eq_primeRank (p := 2) W,hsize,
    IsElementaryAbelian.log_card_eq_primeRank (p := 2) W₂]
  exact hfour

end CFSG.Quasithin.Chapter14.Section06
