module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBaumann
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.ShortSeedPropagation
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup

/-!
# Propagating the literal right block to the maximal Cartan component

The right residual is normalized by the two-core of the maximal A₇
component and normally generates that component modulo its two-core.
The earlier short-seed propagation theorem therefore makes the component
short. Applying the normal-module support theorem on both sides identifies
both intrinsic block layers with the original four-space. The full local
two-core commutator with the maximal component is this same space.

These are the block-propagation and chief-factor support steps of 5.1.13.
No right-block exclusion or unconditional Cartan-escape theorem is asserted.
The companion LocalChief module uses these identities on the original
Sylow intersection, without changing the cubic or either quotient map.
Source: Aschbacher–Smith 5.1.13, printed p.638, and C.1.21, printed p.128,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The block on the literal right residual propagates to the actual maximal
A7 component, through the original two-core-normalized inclusion. -/
theorem LocalA7Configuration.short_of_right_block
    {T : Sylow 2 G} {L W H A Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : LocalCartanWitness T H A Y X D)
    (hb : ChapterC.IsChiBlockIn (pResidual 2 H)) : ChapterC.IsShort K := by
  let R := (residual H).subgroupOf K
  have hRK := d.residual_le.trans a.contains
  let eR : R ≃* pResidual 2 H := (subgroupOfEquivOfLe hRK).trans
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  have hR : ChapterC.IsShort R := hb.1.short.of_mulEquiv eR.symm
  have hcoreT : K.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hc := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K)
      ((pCoreIn_le 2 K).trans (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left))
      ((sup_le K.le_normalizer a.sylow_normalizes).trans
        (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
    exact hc.trans ((pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right))
  have hQR : pCore 2 K ≤ normalizer (R : Set K) := by
    apply le_normalizer_iff.mpr
    intro q hq r hr
    exact le_normalizer_iff.mp (le_normalizer_residual H)
      q.val (hH.1.1.2 (hcoreT (mem_map_of_mem K.subtype hq))) r.val hr
  let := LocalOmega.quotient_quasisimple a.maximal.1 (Or.inl a.quotient)
  have hp := Chapter1.Section02.Adequate.mem_L_isPPerfect a.maximal.1
  have hf : generalizedFitting K = pCore 2 K :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T (h.qtke.evenCharacteristic T) a.maximal.1)
  have hn : ¬ R.map (QuotientGroup.mk' (pCore 2 K)) ≤ center (K ⧸ pCore 2 K) := by
    intro hc
    rw [LocalOmega.quotient_center a.maximal.1 (Or.inl a.quotient)] at hc
    have hRcore : R ≤ pCore 2 K := by
      have hh := map_le_iff_le_comap.mp hc
      change R ≤ (QuotientGroup.mk' (pCore 2 K)).ker at hh
      rwa [QuotientGroup.ker_mk'] at hh
    have hrp : IsPGroup 2 R := pCore_isPGroup.to_le hRcore
    have h5 : 5 ∣ Nat.card R := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hRK).toEquiv]
      exact d.five_dvd_residual
    obtain ⟨k,hk⟩ := hrp.exists_card_eq
    rw [hk] at h5
    have hh := (by decide : Nat.Prime 5).dvd_of_dvd_pow h5
    norm_num at hh
  exact ChapterC.RankOne.GlaubermanArgument.isShort_of_normal_generation R hR hp hf
    (Or.inl inferInstance) hQR
    (ChapterC.RankOne.GlaubermanArgument.normal_generation_of_noncentral_core_image R hp hn)

/-- Both intrinsic block layers are the same original four-space. In the
maximal join it is also the full core commutator with the component. -/
theorem LocalA7Configuration.right_block_layers
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hb : ChapterC.IsChiBlockIn (pResidual 2 H)) :
    (ChapterC.blockU (pResidual 2 H)).map (H.subtype.comp (pResidual 2 H).subtype) =
        localOmegaModule T K ∧
      (ChapterC.blockU K).map K.subtype = localOmegaModule T K ∧
      ⁅(K ⊔ (T : Subgroup G)).pCoreIn 2,K⁆ = localOmegaModule T K := by
  have hc := a.four h hH hgen c d
  have hne : localOmegaModule T K ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hc
    contradiction
  have hs := a.right_omega_span_reduced h hH hgen c d
  have hVH : localOmegaModule T K ≤ H := by
    rw [←hs.1]
    exact conjugateSpanBy_le_self
      ((show omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) from fun z hz =>
        ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans hH.1.1.2)
  let V := (localOmegaModule T K).subgroupOf H
  let := hs.2.1.normal
  let := hs.2.1.elementary
  have heH := ChapterC.RankOne.ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator
    (pResidual 2 H) V hb.1 (by
      rw [hs.2.2]
      intro he
      apply hne
      have hh := congrArg (map H.subtype) he
      rwa [map_subgroupOf_eq_of_le hVH,Subgroup.map_bot] at hh)
  have hright : (ChapterC.blockU (pResidual 2 H)).map (H.subtype.comp (pResidual 2 H).subtype) =
      localOmegaModule T K := by
    rw [←map_map,heH,hs.2.2,map_subgroupOf_eq_of_le hVH]
  let M := K ⊔ (T : Subgroup G)
  let E := K.subgroupOf M
  let U := (localOmegaModule T K).subgroupOf M
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  let : E.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer a.sylow_normalizes)
  let e : E ≃* K := subgroupOfEquivOfLe le_sup_left
  have hbE : ChapterC.IsBlock E := ⟨inferInstance,
    (a.short_of_right_block h hH d hb).of_mulEquiv e.symm,Normal.isSubnormal inferInstance⟩
  have hm : ⁅U,E⁆ = U := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le a.reduced.1,map_subgroupOf_eq_of_le le_sup_left]
    exact LocalOmega.full_movement (h.qtke.evenCharacteristic T) a.maximal.1 a.sylow_normalizes
  have hUe : U ≠ ⊥ := by
    intro he
    apply hne
    have hh := congrArg (map M.subtype) he
    rwa [map_subgroupOf_eq_of_le a.reduced.1,Subgroup.map_bot] at hh
  have heU := ChapterC.RankOne.ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator
    E U hbE (by rw [hm]; exact hUe)
  rw [hm] at heU
  have hmap : ((ChapterC.blockU E).map E.subtype).map M.subtype =
      (ChapterC.blockU K).map K.subtype := by
    rw [map_map]
    change (ChapterC.blockU E).map (K.subtype.comp e.toMonoidHom) = _
    rw [←map_map]
    congr 1
    rw [ChapterC.blockU,ChapterC.blockU,map_commutator,pCore_map_iso,
      map_top_of_surjective _ e.surjective]
  have heK : (ChapterC.blockU K).map K.subtype = localOmegaModule T K := by
    rw [←hmap,heU,map_subgroupOf_eq_of_le a.reduced.1]
  refine ⟨hright,heK,?_⟩
  have hh := congrArg (map M.subtype) hbE.ambient_core_commutator
  rw [map_commutator,map_subgroupOf_eq_of_le le_sup_left,heU,
    map_subgroupOf_eq_of_le a.reduced.1] at hh
  exact hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
