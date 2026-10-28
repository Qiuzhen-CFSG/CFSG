module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLinearThreeCore
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.FourElementField
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Cubic fixed points in the original PSL₃(4) star quotient

Every involution centralizer in the genuine PSL₃(4) is a two-group, so a
cubic subgroup fixes no nonidentity involution. In particular it fixes no
nonidentity element of the long-root group; no Borel marking is required.

The original long-root placement puts the full-module image inside the
simple residual and makes its Sylow intersection centralize that image.
The already identified normal core is O₂(H). Consequently the original
Sylow--residual commutator lies in O₂(H), and an original residual cubic
whose commutator with the full module lies there forces the full module
itself into O₂(H). The latter cubic commutator premise is retained explicitly.

Source: Aschbacher--Smith, E.2.7 and the generation-two argument of 9.3,
printed pp.219,733--735. The intrinsic involution centralizer calculation
is the field-four endpoint of the inner case of 16.4.8, printed p.1188.
-/

public section
open scoped MatrixGroups commutatorElement
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3Even.MinimalParabolicWitness
namespace CFSG.Quasithin.Chapter10.SourceOldResidual.LinearThreeRootAction
variable (F : Type*) [Field F] [Finite F]

/-- Any cubic subgroup of PSL₃(4) fixes only the identity among involutions. -/
theorem involution_eq_one_of_cubic_centralizes
    (hF : Nat.card F = 4) (B : Subgroup PSL(3,F)) (hB : Nat.card B = 3)
    (z : PSL(3,F)) (hz2 : z ^ 2 = 1)
    (hz : z ∈ centralizer (B : Set PSL(3,F))) : z = 1 := by
  by_contra hzne
  have hc : IsPGroup 2 (centralizer ({z} : Set PSL(3,F))) :=
    (Matrix.PSL3.EvenInnerCentralizers.centralizer_isTwoGroup_of_card_four F hF).of_equiv
      (Matrix.PSL3.EvenInnerCentralizers.involutionCentralizerEquiv F
        (n := 2) (by decide) (by simpa using hF) z hzne hz2).symm
  have hBC : B ≤ centralizer ({z} : Set PSL(3,F)) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz b hb)
  have hB2 : IsPGroup 2 B := hc.of_injective (inclusion hBC) (inclusion_injective hBC)
  obtain ⟨n,hn⟩ := hB2.exists_card_dvd_pow
  rw [hB] at hn
  have h := (by decide : Nat.Prime 3).dvd_of_dvd_pow hn
  norm_num at h

/-- The full long-root group has no nonidentity fixed point under any cubic. -/
theorem projectiveCenter_inf_cubic_centralizer_eq_bot [CharP F 2]
    (hF : Nat.card F = 4) (B : Subgroup PSL(3,F)) (hB : Nat.card B = 3) :
    projectiveCenter F ⊓ centralizer (B : Set PSL(3,F)) = ⊥ := by
  apply bot_unique
  rintro z ⟨hz,hc⟩
  apply mem_bot.mpr
  apply involution_eq_one_of_cubic_centralizes F hF B hB z ?_ hc
  obtain ⟨c,rfl⟩ := (mem_projectiveCenter F z).mp hz
  rw [← map_pow, (square_eq_one_iff F _).mpr (Or.inl rfl), map_one]

/-- Transport to elementary and cubic subgroups of the same actual matrix subgroup. -/
theorem elementary_eq_bot_of_cubic_centralizes
    (hF : Nat.card F = 4) {X : Type*} [Group X]
    (K V B : Subgroup X) (e : K ≃* PSL(3,F))
    (hVK : V ≤ K) (hBK : B ≤ K) [IsElementaryAbelian 2 V]
    (hB : Nat.card B = 3) (hc : B ≤ centralizer (V : Set X)) : V = ⊥ := by
  let B' := (B.subgroupOf K).map e.toMonoidHom
  have hB' : Nat.card B' = 3 := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv, hB]
  apply bot_unique
  intro z hz
  apply mem_bot.mpr
  have hz' : e (⟨z,hVK hz⟩ : K) = 1 := by
    apply involution_eq_one_of_cubic_centralizes F hF B' hB' _
    · rw [← map_pow]
      have hp : (⟨z,hVK hz⟩ : K)^2 = 1 :=
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz)
      rw [hp,map_one]
    · apply mem_centralizer_iff.mpr
      rintro _ ⟨b,hb,rfl⟩
      have hcomm : b * (⟨z,hVK hz⟩ : K) = (⟨z,hVK hz⟩ : K) * b :=
        Subtype.ext ((mem_centralizer_iff.mp (hc hb) z hz).symm)
      simpa only [MulEquiv.coe_toMonoidHom,map_mul] using congrArg e hcomm
  exact congrArg Subtype.val (e.injective (hz'.trans e.map_one.symm))

end CFSG.Quasithin.Chapter10.SourceOldResidual.LinearThreeRootAction

namespace CFSG.Quasithin.Chapter10.SourceOldResidual
open ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem cubic_card_map_quotient
    (N B : Subgroup X) [N.Normal] (hN : IsPGroup 2 N) (hB : Nat.card B = 3) :
    Nat.card (B.map (QuotientGroup.mk' N)) = 3 := by
  let f := (QuotientGroup.mk' N).comp B.subtype
  have h3 : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hd : Disjoint B N := h3.disjoint_of_coprime hN (by decide)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro b hb
    apply mem_bot.mpr
    apply Subtype.ext
    exact hd.le_bot ⟨b.property, (QuotientGroup.eq_one_iff _).mp hb⟩
  have hr : f.range = B.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, hB]

/-- Original long-root placement gives residual containment and Sylow centralization. -/
theorem linear_three_star_module_geometry
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hs : ¬Group.IsSolvable X) (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hm : ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax S hP) K) 3 4)
    (V : Subgroup X) [IsElementaryAbelian 2 V]
    (hVS : V ≤ (S : Subgroup X)) (hVN : (S : Subgroup X) ≤ normalizer (V : Set X)) :
    let q := QuotientGroup.mk' (minimalParabolicCore S hP)
    V.map q ≤ K.map q ∧
      ((S : Subgroup X).map q ⊓ K.map q) ≤ centralizer (V.map q : Set _) := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let V' := V.map q
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.map q
  have hi := ChapterE.Structure.source_normal_simple_image S hP hs K hK hgen
  let : IsSimpleGroup (K.map q) := hi.1
  let : (K.map q).Normal := hi.2.2.1
  have hstar := ChapterE.Structure.source_star_minimal_core_free S hP
  have hm' : ClassicalGroup.IsPSL (K.map q) 3 4 := hm
  obtain ⟨F,hfld,hfin,hF,⟨eF⟩⟩ := hm'
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by norm_num [← Nat.card_eq_fintype_card, hF])
  obtain ⟨g,hU,_,hVroot⟩ := ChapterE.Structure.LinearThree.exists_longRoot_placement
    F (n := 2) (by decide) (by simpa using hF) (K.map q) eF S'
    hi.2.2.2 hstar.1 hstar.2 V' (map_mono hVS)
    ((map_mono hVN).trans (V.le_normalizer_map q))
  let f := modelEmbedding F (K.map q) (eF.trans (MulAut.conj g))
  have hfr : f.range = K.map q := modelEmbedding_range F _ _
  refine ⟨hVroot.trans (show (projectiveCenter F).map f ≤ K.map q from
    (map_le_range f (projectiveCenter F)).trans hfr.le), ?_⟩
  intro z hz
  apply mem_centralizer_iff.mpr
  intro v hv
  obtain ⟨u,rfl⟩ := hfr.symm ▸ hz.2
  have hu : u ∈ unipotent F := hU ▸ hz.1
  obtain ⟨w,hw,rfl⟩ := hVroot hv
  obtain ⟨a,ha⟩ := (projective_range F).symm ▸ hu
  obtain ⟨c,hc⟩ := (mem_projectiveCenter F w).mp hw
  have hcomm : w * u = u * w := by
    rw [← ha, ← hc, ← map_mul, ← map_mul]
    apply congrArg (projective F)
    apply (mul_comm_iff F _ _).mpr
    simp
  simpa only [map_mul] using congrArg f hcomm

end CFSG.Quasithin.Chapter10.SourceOldResidual

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Theory.GroupTheory Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

private theorem original_star_geometry
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax
        (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4) :
    let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
    let q := QuotientGroup.mk' (minimalParabolicCore (T.subtype hH.1.1.2) hP)
    (D.fullModule.subgroupOf H).map q ≤ (pResidual 2 H).map q ∧
      (((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H).map q ⊓ (pResidual 2 H).map q) ≤
        centralizer ((D.fullModule.subgroupOf H).map q : Set _) := by
  have hVH : D.fullModule ≤ H := m.fullModule_le_sylow.trans hH.1.1.2
  let := m.fullModule_elementary
  let : IsElementaryAbelian 2 (D.fullModule.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hVH
  have hs : ¬Group.IsSolvable H := by
    intro hh
    let := hh
    exact (Nat.not_le_of_gt hlarge) generationParameter_le_one_of_solvable
  have hVS : D.fullModule.subgroupOf H ≤ ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) :=
    comap_mono m.fullModule_le_sylow
  have hVN : ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ≤
      normalizer (D.fullModule.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hVH]
    exact comap_mono ((le_normalizer_componentOrbit L T).trans
      D.maximalLocal_normalizes_fullModule)
  exact SourceOldResidual.linear_three_star_module_geometry _ _ hs _ hK
    (pResidual_sup_sylow_eq_top _) hm _ hVS hVN

/-- The original Sylow intersection with the residual centralizes V modulo O₂(H). -/
theorem old_residual_linear_three_sylow_residual_commutator_le_twoCore
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax
        (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4) :
    ⁅(T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype, D.fullModule⁆ ≤ H.pCoreIn 2 := by
  let S := T.subtype hH.1.1.2
  let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let R := (T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype
  let V := D.fullModule.subgroupOf H
  have hVH : D.fullModule ≤ H := m.fullModule_le_sylow.trans hH.1.1.2
  have hRH : R ≤ H := inf_le_right.trans (map_subtype_le _)
  have hRS : R.subgroupOf H ≤ (S : Subgroup H) := comap_mono inf_le_left
  have hRK : R.subgroupOf H ≤ pResidual 2 H := by
    have hh := comap_mono (f := H.subtype) (show R ≤ (pResidual 2 H).map H.subtype from inf_le_right)
    change R.subgroupOf H ≤ ((pResidual 2 H).map H.subtype).comap H.subtype at hh
    simpa only [comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hgeo := (m.original_star_geometry hH hlarge hK hm).2
  have hc : (R.subgroupOf H).map q ≤ centralizer (V.map q : Set _) :=
    (le_inf (map_mono hRS) (map_mono hRK)).trans hgeo
  have hr : ⁅R.subgroupOf H,V⁆ ≤ J := by
    apply commutator_le.mpr
    intro r hr v hv
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅r,v⁆ = 1
    rw [map_commutatorElement]
    exact mem_centralizer_iff_commutator_eq_one'.mp (hc (mem_map_of_mem q hr)) _
      (mem_map_of_mem q hv)
  have he := map_mono (f := H.subtype) hr
  rw [map_commutator,map_subgroupOf_eq_of_le hRH,map_subgroupOf_eq_of_le hVH] at he
  have hJ : J = pCore 2 H := m.old_residual_linear_three_core_eq_twoCore hH hlarge hK hm
  rw [hJ] at he
  exact he

/-- A residual cubic centralizing the original V-image forces V into O₂(H). -/
theorem old_residual_linear_three_fullModule_le_twoCore_of_cubic_commutator
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax
        (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4)
    (B : Subgroup G) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hB : Nat.card B = 3) (hcomm : ⁅B,D.fullModule⁆ ≤ H.pCoreIn 2) :
    D.fullModule ≤ H.pCoreIn 2 := by
  let S := T.subtype hH.1.1.2
  let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let V := D.fullModule.subgroupOf H
  let B₀ := B.subgroupOf H
  let B' := B₀.map q
  let V' := V.map q
  have hJ : J = pCore 2 H := m.old_residual_linear_three_core_eq_twoCore hH hlarge hK hm
  have hBH : B ≤ H := hBK.trans (map_subtype_le _)
  have hVH : D.fullModule ≤ H := m.fullModule_le_sylow.trans hH.1.1.2
  let := m.fullModule_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.map q
  have hB₀ : Nat.card B₀ = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv).trans hB
  have hB' : Nat.card B' = 3 :=
    SourceOldResidual.cubic_card_map_quotient J B₀ (hJ ▸ pCore_isPGroup) hB₀
  have hB₀K : B₀ ≤ pResidual 2 H := by
    have hh := comap_mono (f := H.subtype) hBK
    change B₀ ≤ ((pResidual 2 H).map H.subtype).comap H.subtype at hh
    simpa only [comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hcommH : ⁅B₀,V⁆ ≤ J := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hVH,hJ]
    exact hcomm
  have hc : B' ≤ centralizer (V' : Set _) := by
    rintro b ⟨b,hb,rfl⟩
    apply mem_centralizer_iff_commutator_eq_one'.mpr
    rintro v ⟨v,hv,rfl⟩
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcommH (commutator_mem_commutator hb hv))
  have hm' : ClassicalGroup.IsPSL ((pResidual 2 H).map q) 3 4 := hm
  obtain ⟨F,hfld,hfin,hF,⟨eF⟩⟩ := hm'
  have hvbot : V' = ⊥ :=
    SourceOldResidual.LinearThreeRootAction.elementary_eq_bot_of_cubic_centralizes
      F hF ((pResidual 2 H).map q) V' B' eF
      (m.original_star_geometry hH hlarge hK hm).1 (map_mono hB₀K) hB' hc
  have hVJ : V ≤ J := by
    intro v hv
    apply (QuotientGroup.eq_one_iff _).mp
    exact mem_bot.mp (hvbot ▸ mem_map_of_mem q hv)
  have he := map_mono (f := H.subtype) hVJ
  rw [map_subgroupOf_eq_of_le hVH,hJ] at he
  exact he

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
