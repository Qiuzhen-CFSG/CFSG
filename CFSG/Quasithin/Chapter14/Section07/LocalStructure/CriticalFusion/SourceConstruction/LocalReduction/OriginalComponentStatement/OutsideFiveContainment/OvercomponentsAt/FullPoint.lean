module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt.Models
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt.FiveNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentSieveAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.PlaneContradiction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveSectionTernarySieve
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.PResidual.NormalizedImageContainment

/-!
# The actual outside A₅ is a component of the full point stabilizer

Source 1.2.4 constructs its normalized containing component. The literal
proper local A₅ section in that component's two-core image and the original
source catalogue force A₇. That containing component includes the original
point residual, whose two-perfect normalizer action then places it back in
the original A₅. This contradicts the outside hypothesis, so no enlargement
occurred. Every quotient and inclusion is induced by the original groups.
Source: Aschbacher–Smith 14.7.45(2), printed pp.1062–1063.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Source 14.7.45 for the original outside alternating-five component;
its full-point component placement is proved, rather than assumed. -/
theorem outside_five_is_full_point_component_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map I.subtype) :
    ((C.map I.subtype).subgroupOf F.H).IsCComponent := by
  let K := C.map I.subtype
  have hKI : K ≤ I := map_subtype_le _
  have hc : (K.subgroupOf I).IsCComponent := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hn := local_cComponent_normal_at d h hab structural previous faithful earlier
    I K hI hKI hc
  have hIK : I ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKI).mp hn
  have hTK := (F.sylow_le_of_mem_Hz hI).trans hIK
  have hAK := (F.Li_one_le_of_mem_Hz hI).trans hIK
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hKH : K ≤ F.H := hKI.trans hI.2.1
  have hKL : K ∈ Chapter1.L G (T : Subgroup G) := Chapter1.mem_L_of_cComponent hI.1.1
    ⟨T.subtype (F.sylow_le_of_mem_Hz hI),by
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)]⟩ hKI hc
  let B := K.subgroupOf F.H
  let S := T.subtype hTH
  have hB : B ∈ Chapter1.L F.H (S : Subgroup F.H) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTH hKH).mp ⟨hKH,hKL⟩
  have hSB : (S : Subgroup F.H) ≤ normalizer (B : Set F.H) := by
    rw [←subgroupOf_normalizer_eq hKH]
    exact subgroupOf_mono F.H hTK
  obtain ⟨D,⟨hD,hBD,hnD⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (local_star_sqtk h F.H hH) S hB hSB
  by_cases he : B = D
  · change B.IsCComponent
    rw [he]
    exact hD
  have hlt : B < D := lt_of_le_of_ne hBD he
  let eCK : C ≃* K := C.equivMapOfInjective I.subtype I.subtype_injective
  let eBC : B ≃* C := (subgroupOfEquivOfLe hKH).trans eCK.symm
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ eBC (pCore_map_iso 2 eBC)).trans eC
  let q := QuotientGroup.mk' (pCore 2 F.H)
  let Dq := D.map q
  let Bq := B.map q
  have hDq := WholeResidualAssembly.GuardedSource.local_component_star_isComponent
    h hab structural previous faithful F.H hH D hD
  let : IsQuasisimple Dq := hDq.2
  obtain ⟨P,hP,hlocal,hPB,hproper,⟨eb⟩⟩ := proper_five_section_in_containing_image
    S B D hD hB.1 hlt hSB eB
  have hm := local_component_binary_rank_one_or_rows_at d h hab structural previous faithful
    earlier F.H hH D hD
  have hmodels : (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSL Dq 2 (2^n)) ∨
      WholeResidualAssembly.ComponentRows Dq := by
    rcases hm with ⟨n,hn,hm⟩ | ⟨_,hm⟩
    · exact Or.inl ⟨n,hn,hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hD).symm⟩
    · exact Or.inr (hm.of_equiv (cComponentTwoCoreQuotientEquiv hD))
  obtain ⟨ed⟩ := proper_five_section_rows_seven P (Bq.subgroupOf Dq) hlocal hproper eb hmodels
  let eD := (cComponentTwoCoreQuotientEquiv hD).trans ed
  have hAD : F.Li L 1 ≤ D.map F.H.subtype :=
    local_binary_alternating_component_contains_point_at h hab structural previous faithful
      F.H hH D hD (Or.inr rfl) eD
  let A := (F.Li L 1).subgroupOf F.H
  have hAH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hAD' : A ≤ D := by
    change (F.Li L 1).subgroupOf F.H ≤ D
    have hh := subgroupOf_mono F.H hAD
    simpa only [subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using hh
  have hpA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 _).of_surjective
    (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hAB : A ≤ normalizer (B : Set F.H) := by
    rw [←subgroupOf_normalizer_eq hKH]
    exact subgroupOf_mono F.H hAK
  let Aq := A.map q
  have hAqD : Aq ≤ Dq := map_mono hAD'
  have hpAq : IsPPerfect 2 (Aq.subgroupOf Dq) :=
    (hpA.of_surjective (q.subgroupMap A) (q.subgroupMap_surjective A)).of_surjective
      (subgroupOfEquivOfLe hAqD).symm.toMonoidHom
      (subgroupOfEquivOfLe hAqD).symm.surjective
  have hAqB : Aq.subgroupOf Dq ≤ normalizer (Bq.subgroupOf Dq : Set Dq) := by
    rw [←subgroupOf_normalizer_eq (map_mono hBD)]
    exact subgroupOf_mono Dq ((map_mono hAB).trans (le_normalizer_map q))
  have hke : IsPGroup 2 ed.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr ed.injective]
    exact IsPGroup.of_card (n := 0) (by simp)
  have ha := twoPerfect_le_local_five_of_seven_quotient ed.toMonoidHom ed.surjective hke
    P (Bq.subgroupOf Dq) hlocal hPB eb (Aq.subgroupOf Dq) hpAq hAqB
  have hAfBf : A.map q ≤ B.map q := by
    change Aq ≤ Bq
    have hh := map_mono (f := Dq.subtype) ha
    simpa only [map_subgroupOf_eq_of_le hAqD,map_subgroupOf_eq_of_le (show Bq ≤ Dq from map_mono hBD)] using hh
  have haB : A ≤ B := isPPerfect_le_of_map_le_of_kernel_normalizes q A B hpA
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    (by rw [QuotientGroup.ker_mk']; exact (pCore_isPGroup.le_sylow_of_normal S).trans hSB) hAfBf
  apply (hout ?_).elim
  have hh := map_mono (f := F.H.subtype) haB
  change ((F.Li L 1).subgroupOf F.H).map F.H.subtype ≤ (K.subgroupOf F.H).map F.H.subtype at hh
  simpa only [map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hKH] using hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
