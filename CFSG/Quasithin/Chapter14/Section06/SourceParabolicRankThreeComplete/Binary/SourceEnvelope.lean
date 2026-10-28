module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Binary.ModuleEnvelope
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceFourSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCenter

/-!
# A narrow binary MS envelope for the original second parabolic

A fully moved subgroup U of the omega-center of O₂(C ∨ R) lies in Z(msQ C R).
For an abelian MS core, the proved source alternatives provide a natural or
doubled-natural envelope; the noncentral Sylow omega-center excludes the
fixed-line alternative. For a nonabelian core the critical distance is even
and greater than two. At distance four the entire center is natural. At larger
distance only [Z(msQ C R),C] is needed, since [U,C] = U.

The last section is transported from the literal join through its subgroup
inclusion, with the CommonFacts quotient marking and its conjugation action.
No equality or ambient centrality of the whole fixed factor is required.
The actual consumer is Binary.SourceComplete for original 14.6.10(5).
Source: Meierfrankenfeld--Stellmacher (1993), (4.5)--(4.6), printed pp.895--912;
Aschbacher--Smith, original 14.6.10(5), printed p.1029.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06.Binary
open ChapterC
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- Transport just the natural moved center through the literal join inclusion. -/
theorem natural_moved_center_of_large_distance {C R : Subgroup G}
    (h : SmallMSPair κ C R)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical) :
    ∃ f : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      HasSectionModel C ⁅FullSieve.SourceInterface.centerIn (msQ C R),C⁆ ⊥
        (linearThreeActor f) (Representation.specialLinearNatural (k := ZMod 2) 3) := by
  obtain ⟨_,_,_,hU⟩ := t.center_source_sections common hb
  let J := C ⊔ R
  let Uc := ⁅FullSieve.SourceInterface.centerIn (msQ C R),C⁆
  have hZjoin : FullSieve.SourceInterface.centerIn (msQ C R) ≤ J :=
    (map_subtype_le (center (msQ C R))).trans (msQ_le_join C R)
  have hUjoin : Uc ≤ J := (@Subgroup.commutator_le_sup G _ _ _).trans
    (sup_le hZjoin le_sup_left)
  have hUsub : ⁅FullSieve.SourceInterface.centerIn
      (msQ (C.subgroupOf J) (R.subgroupOf J)),C.subgroupOf J⁆ = Uc.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_commutator,msQ_subgroupOf le_sup_left le_sup_right,
      centerIn_subgroupOf (msQ_le_join C R),map_subgroupOf_eq_of_le hZjoin,
      map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le hUjoin]
  rw [hUsub] at hU
  let i := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let c := QuotientGroup.congr _ _ i.symm (pCore_map_iso 2 i.symm)
  let em := (h.binaryInput e).quotientEquiv.trans common.natural.marking
  let f := c.trans em
  let a := linearThreeActor f
  have hactor : linearThreeActor em = a.comp i.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change em (QuotientGroup.mk' _ x) = em (c (QuotientGroup.mk' _ (i x)))
    change em (QuotientGroup.mk' _ x) = em (QuotientGroup.mk' _ (i.symm (i x)))
    rw [i.symm_apply_apply]
  rw [hactor] at hU
  refine ⟨f,?_⟩
  apply HasSectionModel.of_subgroupOf (J := J) le_sup_left hUjoin bot_le a _
  simpa only [bot_subgroupOf] using hU

/-- A fully moved omega-center subgroup of the actual small MS pair has a
natural or doubled-natural envelope when the Sylow omega-center is noncentral. -/
theorem envelope_of_smallMSPair (C R S U : Subgroup G)
    (h : SmallMSPair κ C R)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hS : Chapter1.IsSylowIn 2 S (C ⊔ R)) (hRS : R ≤ S)
    (hU : U ≤ omegaOneCenterAmbient ((C ⊔ R).pCoreIn 2))
    (hm : ⁅U,C⁆ = U)
    (hnc : ¬ FullSieve.SourceInterface.omegaCenterIn S ≤
      FullSieve.SourceInterface.centerIn (C ⊔ R)) : ModuleEnvelope C U := by
  classical
  by_cases hc : IsMulCommutative (msQ C R)
  · obtain ⟨f,hf⟩ := h.abelian_source e hc S hS hRS
    exact envelope_of_module_alternatives C R S U f hf hU hm hnc
  have hZ := moved_omega_le_center_msQ C R U hU hm
  have hc' : ¬ IsMulCommutative (BinaryMS.commutatorCore (C.subgroupOf (C ⊔ R))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv C R).symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hh
      ((binaryCoreEquiv C R).symm x) ((binaryCoreEquiv C R).symm y)
  obtain ⟨t⟩ := BinaryMS.MS93.exists_setup (h.binaryInput e) hc'
  obtain ⟨common⟩ := t.commonFacts hc'
  by_cases hb : t.geometry.b t.reduction.radical = 4
  · obtain ⟨f,hf,_⟩ := h.distance_four_source_sections e t common hb
    exact ⟨FullSieve.SourceInterface.centerIn (msQ C R),f,hZ,Or.inl hf⟩
  have hb' : 4 < t.geometry.b t.reduction.radical := by
    have he := t.geometry.even (BinaryMS.MS93.alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at he
    obtain ⟨n,hn⟩ := he
    have hl := common.large_distance
    omega
  obtain ⟨f,hf⟩ := natural_moved_center_of_large_distance h e t common hb'
  exact ⟨⁅FullSieve.SourceInterface.centerIn (msQ C R),C⁆,f,
    hm ▸ commutator_mono hZ le_rfl,Or.inl hf⟩

end CFSG.Quasithin.Chapter14.Section06.Binary
