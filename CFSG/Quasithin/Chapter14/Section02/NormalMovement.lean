module
public import CFSG.Quasithin.Chapter14.Section02.LargeBenderSource
public import CFSG.Quasithin.Chapter14.Section02.NormalBorel
public import Theory.GroupTheory.Commutator.PrimeImage
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# The source exclusion of a normal S₂

For the original normal component, S₂ contains its Sylow intersection
and normalizes it, so S₂ is Sylow in O²(H)S₂. It is nontrivial by the
proper rank-one Sylow normalizer. If Y normalized S₂, the completed
original common-normal theorem 3.1.1 would contradict the unique maximal
two-local overgroup of YT. All inputs come from the original plane source.

Source: Aschbacher--Smith 14.2.14, printed p.984.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_normal_amalgam_not_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (hres : pResidual 2 H = K)
    (hq : ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K)) :
    let Y := sourceResidual M Mc
    let K₁ := K.map H.subtype
    let R := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K₁)
    ¬Y ≤ normalizer (R : Set G) := by
  let Y := sourceResidual M Mc
  let K₁ := K.map H.subtype
  let R := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K₁)
  let X := Y ⊔ (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let TH := T.subtype hTH
  obtain ⟨hS,hQ,hR,_⟩ := source_normal_amalgam_core hG T hempty hM hu hmany hcard e H hH K hgen
  have hRT : R ≤ (T : Subgroup G) := hR.trans_eq hS
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  have hMY : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sourceResidual_le _ _)).mp (residualY_normal M Mc)
  have hHN : H ≤ normalizer (K₁ : Set G) := by
    have hh := K.le_normalizer_map H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hTK : (T : Subgroup G) ≤ normalizer (K₁ : Set G) := hTH.trans hHN
  have hTI : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ K₁ : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),
      le_normalizer_iff.mp hTK t ht x hx.2⟩
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf ((hM.1.2.trans hMY).trans
      (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))) hTI).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨P,hP⟩ := TH.exists_sylow_map_eq_inf_of_normal K
  have hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ K₁) K₁ := by
    have hh := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr
      (show Chapter1.IsSylowIn 2 ((TH : Subgroup H) ⊓ K) K from ⟨P,hP⟩)
    simpa only [TH,Subgroup.map_inf _ _ _ H.subtype_injective,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH] using hh
  have hne : R ≠ ⊥ := by
    intro hr
    have hTKzero : (T : Subgroup G) ⊓ K₁ = ⊥ := le_bot_iff.mp (hr ▸ le_sup_right)
    have hPk : (P : Subgroup K) = ⊥ := by
      apply ((P : Subgroup K).map_eq_bot_iff_of_injective K.subtype_injective).mp
      apply (((P : Subgroup K).map K.subtype).map_eq_bot_iff_of_injective H.subtype_injective).mp
      rw [hP]
      simpa only [TH,Subgroup.map_inf _ _ _ H.subtype_injective,Sylow.coe_subtype,
        map_subgroupOf_eq_of_le hTH] using hTKzero
    have hp := (ChapterF.Source.rankOneSylowFacts_of_rankOneQuotient hq P).proper
    change normalizer ((P : Subgroup K) : Set K) < ⊤ at hp
    have he : normalizer ((P : Subgroup K) : Set K) = ⊤ := by
      rw [hPk]
      exact normalizer_eq_top (⊥ : Subgroup K)
    exact hp.ne he
  change ¬Y ≤ normalizer (R : Set G)
  intro hYR
  have hXR : X ≤ normalizer (R : Set G) := sup_le hYR hTR
  have hXH : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right hXM
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  obtain ⟨P₁,hP₁⟩ := hSyl
  have hRsy : Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) := by
    rw [hres]
    exact (T.isPGroup'.to_le hRT).exists_sylow_sup_of_coprime_index K₁ R
      (hRT.trans hTK) (P₁ : Subgroup K₁) P₁.not_dvd_index (hP₁ ▸ le_sup_right)
  have hcommon := Chapter3.source_common_normal_knownSimple hG T X H R hXH hH.1.1
    (Chapter3.HStar.hasUniqueMaximalOver T hM.1.2 hH) hne hRT hRsy hXR
  obtain ⟨_,_,_,_,_,_,hunique,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  exact Chapter3.no_common_normal_of_unique_maximal (T.isPGroup'.to_le hRT)
    (fun L hL hXL => Set.mem_singleton_iff.mp (hunique ▸ (show L ∈ maximalTwoLocalOvergroups X from ⟨hL,hXL⟩)))
    hH.1.2 hcommon
end CFSG.Quasithin.Chapter14.Section02
