module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionSourceEndgame
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionSourceResidual

/-!
# LocalAnalysisNaturalFourExclusionSourceEndgame at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionSourceEndgame`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

private theorem source_perfect_span_at (z : G) :
    conjugateSpanBy (S.fourComponentPointPerfect z) (S.fourPointLocal z) =
      S.fourComponentPointPerfect z :=
  le_antisymm (conjugateSpanBy_le le_rfl S.four_componentPointPerfect_normalized)
    (le_conjugateSpanBy _ _)

theorem four_componentPointPerfect_normalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourPointCentralizer z ⊓ normalizer (S.fourComponentPointPerfect z : Set G) =
      S.fourPointLocal z := by
  have h := (S.four_component_pushingUp_at structural e hd hz hz1 hzT).normalizer_span_eq
  rwa [S.source_perfect_span_at] at h

theorem four_componentPointPerfect_sectionCentralizer_le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ChapterA.Section04.twoSectionCentralizer (S.fourComponentPointPerfect z)
      (S.fourPointCentralizer z) ≤ S.fourPointLocal z := by
  have h := (S.four_component_pushingUp_at structural e hd hz hz1 hzT).section_le_local
  rwa [S.source_perfect_span_at] at h

theorem four_componentPointPerfect_not_normalized_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ¬ S.fourPointCentralizer z ≤ normalizer (S.fourComponentPointPerfect z : Set G) := by
  intro hn
  have hm := S.four_componentPointPerfect_normalizer_at structural e hd hz hz1 hzT
  rw [inf_eq_left.mpr hn] at hm
  apply S.four_all_pointCentralizers_escape escape e hd hz hz1
  exact hm.le.trans inf_le_left

theorem four_componentPointPerfect_not_cComponent_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourComponentPointPerfect z ∉ Chapter1.cComponentsIn (S.fourPointCentralizer z) := by
  intro hb
  let H := S.fourPointCentralizer z
  let D := S.fourComponentPointPerfect z
  have hTH : (T : Subgroup G) ≤ H := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)
  have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    (le_inf S.chosen.sylow_normalizes_component hTH).trans
      S.four_componentPointPerfect_normalized
  let d := subgroupOfEquivOfLe hb.1
  let q := d.toMonoidHom.pCoreQuotientEquiv (p := 2) d.surjective
    (by rw [d.toMonoidHom.ker_eq_bot d.injective]; exact IsPGroup.of_bot)
  let := Theory.SpecificGroups.LinearHigher.psl_isQuasisimple (F := ZMod 2) (n := 3) (by decide)
  let : IsQuasisimple ((D.subgroupOf H) ⧸ pCore 2 (D.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv (q.trans (S.fourComponentPointCoreEquiv e hd ⟨z,hz⟩
      (fun he => hz1 (congrArg Subtype.val he)))).symm
  have hTN : ((T.subtype hTH) : Subgroup H) ≤ normalizer (D.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hb.1]
    exact comap_mono hTD
  have hn : (D.subgroupOf H).Normal := by
    rcases ChapterC.Section04Constrained.component_orbit_bound
      (S.four_component_pushingUp_at structural e hd hz hz1 hzT).sqtk hb.2 with hn | hi
    · exact hn
    · have hdiv := index_dvd_of_le hTN
      rw [hi] at hdiv
      exact ((T.subtype hTH).not_dvd_index hdiv).elim
  exact S.four_componentPointPerfect_not_normalized_at structural escape e hd hz hz1 hzT
    ((normal_subgroupOf_iff_le_normalizer hb.1).mp hn)

theorem four_module_le_overcomponent_module_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    {K : Subgroup G} (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hDK : S.fourComponentPointPerfect z ≤ K) :
    V ≤ ChapterA.Section04.signalizerModule K ((K ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let D := S.fourComponentPointPerfect z
  let U := ChapterA.Section04.twoSectionCentralizer D (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ S.fourPointCentralizer z := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)
  have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    (le_inf S.chosen.sylow_normalizes_component hTH).trans
      S.four_componentPointPerfect_normalized
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    Chapter1.Section02.Adequate.local_chain_normalizes
      (S.four_componentPointPerfect_local hz hz1 hzT e hd) hKL hDK hTD
  have hQT : S.fourComponentPointCore z ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (D ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hs := S.four_componentPointCore_section_sylow hzT
  have hQU : S.fourComponentPointCore z ≤ U := by
    intro q hq
    exact ⟨hQT hq,((Chapter1.isSylowIn_iff.mp hs).2.1 hq).2⟩
  have he : U = S.fourComponentPointCore z :=
    (Chapter1.isSylowIn_iff.mp hs).2.2 U
      (T.isPGroup'.to_le (ChapterA.Section04.twoSectionCentralizer_le _ _)) hQU
      (fun _ hu => ⟨hTH hu.1,hu.2⟩)
  have hVQ : V ≤ S.fourComponentPointCore z := by
    rw [S.four_componentPointCore_eq_chosenCore_at structural e hd hz hz1 hzT]
    exact S.chosen.le_core
  have hVU : V ≤ omegaCenterIn U := by
    rw [he]
    let := S.chosen.elementary
    have hc := le_centralizer_iff.mp
      (S.four_componentPointCore_centralizes_at structural e hd hz hz1 hzT)
    intro v hv
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hVQ hv,hc hv,elemPow_eq_one_of_isElementaryAbelian v hv⟩
  have hVm : V ≤ ChapterA.Section04.signalizerModule D U := by
    rw [ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter,commutator_comm]
    exact (S.four_componentPointPerfect_moved e hd hz hz1).le.trans
      (commutator_mono hVU le_rfl)
  have hR : (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) (K ⊔ (T : Subgroup G)) := by
    refine ⟨T.subtype le_sup_right,?_⟩
    exact map_subgroupOf_eq_of_le le_sup_right
  have hSylN : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (D : Set G))
      ((K ⊔ (T : Subgroup G)) ⊓ normalizer (D : Set G)) := by
    rw [inf_eq_left.mpr hTD]
    exact hSyl.restrict (le_inf le_sup_right hTD) inf_le_left
  have hKtype := Chapter1.Section02.Adequate.mem_L_isSignalizerType T
    (S.hypothesis.simpleQTKE.evenCharacteristic T) hKL
  exact hVm.trans (ChapterA.Section04.SourceChains.source_A410 D K T hDK
    (S.four_componentPointPerfect_faithful_at structural e hd hz hz1 hzT).1 hKtype hTK
    hSyl (le_inf hR (hR.trans hTD)) hSylN).2.1

theorem four_component_exists_strict_overcomponent_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z) ∧
      S.fourComponentPointPerfect z < K ∧ ¬ K ≤ S.fourPointLocal z ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      ChapterA.Section04.IsFaithfulSignalizerType K ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      V ≤ ChapterA.Section04.signalizerModule K ((K ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      z ∈ ChapterA.Section04.signalizerModule K ((K ⊔ (T : Subgroup G)).pCoreIn 2) ⊓
        centralizer (K : Set G) := by
  obtain ⟨K,hK,hDK,_,hKL,hKf,hTK⟩ :=
    S.four_component_exists_unique_overcomponent_at structural e hd hz hz1 hzT
  have hne : S.fourComponentPointPerfect z ≠ K := by
    intro he
    exact S.four_componentPointPerfect_not_cComponent_at structural escape e hd hz hz1 hzT
      (he ▸ hK)
  have hVm := S.four_module_le_overcomponent_module_at structural e hd hz hz1 hzT hKL hDK
  have hzK : z ∈ centralizer (K : Set G) := by
    apply mem_centralizer_iff.mpr
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hK.1 hk)
  refine ⟨K,hK,lt_of_le_of_ne hDK hne,?_,hKL,hKf,hTK,hVm,⟨hVm hz,hzK⟩⟩
  intro hKM
  have hcompK : (K.subgroupOf (S.fourPointLocal z)).IsCComponent :=
    hK.2.subgroupOf_of_le hKM inf_le_right
  have hcompD := S.four_componentPointPerfect_component e hd ⟨z,hz⟩
    (fun he => hz1 (congrArg Subtype.val he))
  have he := hcompD.eq_of_le hcompK (comap_mono hDK)
  have hm := congrArg (map (S.fourPointLocal z).subtype) he
  rw [map_subgroupOf_eq_of_le hKM] at hm
  have hDM : S.fourComponentPointPerfect z ≤ S.fourPointLocal z :=
    (map_subtype_le _).trans (inf_le_inf_right _ L.le_normalizer)
  rw [map_subgroupOf_eq_of_le hDM] at hm
  exact hne hm

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

