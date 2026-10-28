module
public import CFSG.Quasithin.Chapter14.Section02.ResidualMovement
public import CFSG.Quasithin.Chapter14.Section02.OutsideParabolic
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# The original second amalgam subgroup in every large branch

The source defines S₂ using the whole residual O²(H), including when K₁
is only one component or a parabolic residual. Its two-part is normalized
by T. The nontrivial two-core of Y makes S₂ nontrivial. If Y normalized
S₂, the original common-normal theorem would contradict the unique maximal
two-local overgroup of YT. Thus Y=[Y,S₂], and the actual action identifies
(YS₂)/O₂(YS₂) with S₃. Its intersection with T is exactly S₂.

This proves the original 14.2.14 without a component-normality hypothesis.
The separate containment S₂≤N_T(K₁) and the generated-core argument remain
with the selected K₁ branches. Source: Aschbacher--Smith 14.2.14 and the
surrounding verification of F.1.1, printed p.984.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_residual_twoCore_ne_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3)) : (sourceResidual M Mc).pCoreIn 2 ≠ ⊥ := by
  let Y := sourceResidual M Mc
  have hYM : Y ≤ M := sourceResidual_le _ _
  let : (Y.subgroupOf M).Normal := residualY_normal M Mc
  have hself := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe hYM)).mp (normal_core_selfCentralizing
      (hG.evenCharacteristic T M hM.1.1 hM.1.2) (Y.subgroupOf M))
  obtain ⟨_,_,_,_,hmodel,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hYne : Y ≠ ⊥ := by
    intro hb
    obtain ⟨d⟩ := hmodel
    have hc := (Nat.card_congr d.toEquiv).trans (Nat.card_zmod 3)
    change Nat.card ((Y.subgroupOf M).map _) = 3 at hc
    rw [hb,bot_subgroupOf,Subgroup.map_bot,card_bot] at hc
    omega
  intro hb
  have hcore : pCore 2 Y = ⊥ :=
    ((pCore 2 Y).map_eq_bot_iff_of_injective Y.subtype_injective).mp hb
  apply hYne
  apply le_bot_iff.mp
  intro x hx
  have hxc : (⟨x,hx⟩ : Y) ∈ centralizer (pCore 2 Y : Set Y) := by
    intro y hy
    have hy1 : y = 1 := mem_bot.mp (hcore ▸ hy)
    simp only [hy1,one_mul,mul_one]
  have hxcore := hself hxc
  simpa only [hcore,mem_bot,Subtype.ext_iff,Subgroup.coe_one] using hxcore

theorem source_original_amalgam_not_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let Y := sourceResidual M Mc
    let K := (pResidual 2 H).map H.subtype
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
    S₂ ≤ (T : Subgroup G) ∧ (T : Subgroup G) ≤ normalizer (S₂ : Set G) ∧
      ¬Y ≤ normalizer (S₂ : Set G) := by
  let Y := sourceResidual M Mc
  let K := (pResidual 2 H).map H.subtype
  let R := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
  let X := Y ⊔ (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let TH := T.subtype hTH
  have hMY : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sourceResidual_le _ _)).mp (residualY_normal M Mc)
  have hTQ := (hM.1.2.trans hMY).trans
    (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hQT : Y.pCoreIn 2 ≤ (T : Subgroup G) :=
    sup_eq_right.mp (T.is_maximal'
      ((isPGroup_pCoreIn 2 Y).to_sup_of_normal_left' T.isPGroup' hTQ) le_sup_right)
  have hRT : R ≤ (T : Subgroup G) := sup_le hQT inf_le_left
  have hHN : H ≤ normalizer (K : Set G) := by
    have hh := (pResidual 2 H).le_normalizer_map H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hTK := hTH.trans hHN
  have hTI : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),
      le_normalizer_iff.mp hTK t ht x hx.2⟩
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf hTQ hTI).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  refine ⟨hRT,hTR,?_⟩
  intro hYR
  have hRne : R ≠ ⊥ := fun hr =>
    source_residual_twoCore_ne_bot hG T hempty hM hu hmany hcard e
      (le_bot_iff.mp (hr ▸ (show Y.pCoreIn 2 ≤ R from le_sup_left)))
  obtain ⟨P,hP⟩ := TH.exists_sylow_map_eq_inf_of_normal (pResidual 2 H)
  have hsyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ K) K := by
    have hh := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr
      (show Chapter1.IsSylowIn 2 ((TH : Subgroup H) ⊓ pResidual 2 H) (pResidual 2 H)
        from ⟨P,hP⟩)
    simpa only [TH,Subgroup.map_inf _ _ _ H.subtype_injective,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH] using hh
  obtain ⟨P₁,hP₁⟩ := hsyl
  have hRsy : Chapter1.IsSylowIn 2 R (K ⊔ R) :=
    (T.isPGroup'.to_le hRT).exists_sylow_sup_of_coprime_index K R (hRT.trans hTK)
      (P₁ : Subgroup K) P₁.not_dvd_index (hP₁ ▸ le_sup_right)
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  have hXH : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right hXM
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hcommon := Chapter3.source_common_normal_knownSimple hG T X H R hXH hH.1.1
    (Chapter3.HStar.hasUniqueMaximalOver T hM.1.2 hH) hRne hRT hRsy (sup_le hYR hTR)
  obtain ⟨_,_,_,_,_,_,hunique,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  exact Chapter3.no_common_normal_of_unique_maximal (T.isPGroup'.to_le hRT)
    (fun L hL hXL => Set.mem_singleton_iff.mp (hunique ▸
      (show L ∈ maximalTwoLocalOvergroups X from ⟨hL,hXL⟩))) hH.1.2 hcommon

/-- Original 14.2.14 and its actual second-parabolic quotient and Sylow application. -/
theorem source_lemma_14_2_14
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let Y := sourceResidual M Mc
    let K := (pResidual 2 H).map H.subtype
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
    Y = ⁅Y,S₂⁆ ∧
      Nonempty (((Y ⊔ S₂ : Subgroup G) ⧸ pCore 2 (Y ⊔ S₂ : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) ∧
      (T : Subgroup G) ⊓ (Y ⊔ S₂) = S₂ ∧ Chapter1.IsSylowIn 2 S₂ (Y ⊔ S₂) := by
  obtain ⟨hRT,_,hnot⟩ := source_original_amalgam_not_normalizes
    hG T hempty hM hu hmany hcard e H hH
  obtain ⟨hm,hq⟩ := source_residual_actor_movement hG T hempty hM hu hmany hcard e _ hRT le_sup_left hnot
  exact ⟨hm,hq,source_residual_actor_sylow hG T hempty hM hu hmany hcard e _ hRT le_sup_left⟩

end CFSG.Quasithin.Chapter14.Section02
