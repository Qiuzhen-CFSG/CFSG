module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionFaithful
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionCore

/-!
# LocalAnalysisNaturalFourExclusionFaithful at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionFaithful`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

private theorem perfect_le_pointLocal_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    S.fourPointPerfect z ≤ S.fourPointLocal z := by
  rw [S.four_pointLocal_eq_at structural hz hz1]
  exact (map_subtype_le _).trans (map_subtype_le _)

private theorem sylow_le_pointLocal' {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    (T : Subgroup G) ≤ S.fourPointLocal z := by
  refine le_inf S.chosen.sylow_normalizes_component ?_
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)

theorem four_pointPerfect_characteristicTwo_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourPointPerfect z ∈ Chapter1.He G := by
  have hn : ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).Normal :=
    normal_subgroupOf_of_le_normalizer (S.four_pointLocal_normalizes_perfect_at structural hz hz1)
  exact Chapter1.lemma_1_1_3_1 (S.four_pointLocal_characteristicTwo hz hz1 hzT)
    (fun he => S.chosen.ne_bot (bot_unique
      ((S.four_module_le_pointPerfect_at structural e hd hz hz1).trans he.le)))
    (S.perfect_le_pointLocal_at structural hz hz1) hn.isSubnormal

theorem four_module_le_perfectCore_omegaCenter_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ omegaCenterIn ((S.fourPointPerfect z).pCoreIn 2) := by
  let := S.chosen.elementary
  have hKN : S.fourPointPerfect z ≤ normalizer (V : Set G) :=
    (map_subtype_le _).trans ((map_subtype_le _).trans inf_le_left)
  have hVK : V ≤ S.fourPointPerfect z := S.four_module_le_pointPerfect_at structural e hd hz hz1
  have hVc : V ≤ (S.fourPointPerfect z).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVK hKN
  have hTJ : (S.fourPointPerfect z ⊔ (T : Subgroup G) : Subgroup G) ≤
      normalizer (S.fourPointPerfect z : Set G) :=
    sup_le (S.fourPointPerfect z).le_normalizer
      ((S.sylow_le_pointLocal' hzT).trans
        (S.four_pointLocal_normalizes_perfect_at structural hz hz1))
  have hcQ : (S.fourPointPerfect z).pCoreIn 2 ≤ S.fourPointCore z :=
    pCoreIn_mono_of_normalizes le_sup_left hTJ
  have hVcC : V ≤ centralizer ((S.fourPointPerfect z).pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp (hcQ.trans (S.four_pointCore_centralizes_at structural e hd hz hz1 hzT))
  intro v hv
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨hVc hv, hVcC hv, elemPow_eq_one_of_isElementaryAbelian v hv⟩

theorem four_module_le_intrinsicSignalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ ChapterA.Section04.intrinsicSignalizerModule (S.fourPointPerfect z) := by
  rw [ChapterA.Section04.intrinsicSignalizerModule,
    ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter, commutator_comm]
  exact (S.four_pointPerfect_moved e hd hz hz1).le.trans
    (commutator_mono (S.four_module_le_perfectCore_omegaCenter_at structural e hd hz hz1 hzT) le_rfl)

theorem four_pointPerfect_faithful_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ChapterA.Section04.IsFaithfulSignalizerType (S.fourPointPerfect z) := by
  refine ⟨⟨?_, S.four_pointPerfect_twoPerfect z, ?_⟩, ?_⟩
  · exact fun he => S.chosen.ne_bot (bot_unique
      ((S.four_module_le_pointPerfect_at structural e hd hz hz1).trans he.le))
  · exact generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
      (S.four_pointPerfect_characteristicTwo_at structural e hd hz hz1 hzT))
  · exact fun he => S.chosen.ne_bot (bot_unique
      ((S.four_module_le_intrinsicSignalizer_at structural e hd hz hz1 hzT).trans he.le))

theorem four_pointPerfect_local_of_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (component : ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).IsCComponent) :
    S.fourPointPerfect z ∈ Chapter1.L G (T : Subgroup G) := by
  have hTM := S.sylow_le_pointLocal' hzT
  apply Chapter1.mem_L_of_cComponent ?_
    ⟨T.subtype hTM, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM]⟩
    (S.perfect_le_pointLocal_at structural hz hz1) component
  have hV : V ≤ (S.fourPointLocal z).pCoreIn 2 := by
    let := S.chosen.elementary
    apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
      (S.four_module_le_pointLocal hz)
    rw [S.four_pointLocal_eq_at structural hz hz1]
    exact inf_le_left
  exact fun he => S.chosen.ne_bot (bot_unique (hV.trans he.le))

theorem fourResidualData_of_component_control_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (component : ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).IsCComponent)
    (control : ((S.fourPointCore z).subgroupOf (S.fourPointCentralizer z)).characteristicNormalizerClosure ≤
      (S.fourPointLocal z).subgroupOf (S.fourPointCentralizer z))
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    S.FourResidualData z :=
  S.fourResidualData_of_component_control_at structural e hd hz hz1 hzT component control
    (S.four_pointPerfect_faithful_at structural e hd hz hz1 hzT)
    (S.four_pointPerfect_local_of_component_at structural hz hz1 hzT component) quotient

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

