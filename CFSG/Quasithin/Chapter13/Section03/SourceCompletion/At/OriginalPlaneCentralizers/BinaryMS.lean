module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.BinaryMS
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Inspection.LinearThreeField

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.BinaryMS`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

theorem Context.plane_msOddIndexRadical (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) :
    ChapterC.MSOddIndexRadical
      (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (centralizer (d.A : Set G))) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let H := centralizer (d.A : Set G)
  let M := H ⊓ normalizer (L : Set G)
  let R := Q.subgroupOf H
  let P := normalizer (R : Set H)
  have hr := s.core_plane_radical d
  have hPM : P ≤ M.subgroupOf H :=
    (normalizer_le_characteristicNormalizerClosure_self R hr.1).trans
      (s.plane_local_control d).2.2.1
  obtain ⟨S,hQS,hSM⟩ := s.plane_sylow_in_normalizer d
  let Sg := (S : Subgroup H).map H.subtype
  have hSgM : Sg ≤ M := le_inf (map_subtype_le _) hSM
  have he := (s.plane_twoGroup_index d Sg (S.isPGroup'.map _) hQS hSgM).1
  have hSgN : Sg ≤ normalizer (Q : Set G) := by
    change Sg ⊓ centralizer (V : Set G) = Q at he
    rw [←he]
    apply (le_inf Sg.le_normalizer ?_).trans inf_normalizer_le_normalizer_inf
    exact (hSgM.trans (s.plane_local_control d).2.2.2).trans
      (normalizer_le_normalizer_centralizer V)
  have hSP : (S : Subgroup H) ≤ P := by
    change (S : Subgroup H) ≤ normalizer (Q.subgroupOf H : Set H)
    rw [←subgroupOf_normalizer_eq (show Q ≤ H from (s.plane_local_control d).1)]
    intro x hx
    exact hSgN (mem_map_of_mem H.subtype hx)
  refine ⟨P,lt_top_iff_ne_top.mpr ?_,?_,hr.2⟩
  · intro ht
    apply j.input.outside
    intro x hx
    exact hPM (ht ▸ mem_top (⟨x,j.input.component.1 hx⟩ : H))
  · rw [←Nat.not_even_iff_odd,even_iff_two_dvd]
    exact fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le hSP))

noncomputable def Context.component_binaryMS_input (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (e : (J ⧸ pCore 2 J) ≃* SL(3,ZMod 2)) :
    ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple
      (J.subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2))
      (((L ⊔ T).pCoreIn 2).subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2)) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  let J0 := J.subgroupOf D
  let : J0.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le J.le_normalizer j.input.normalizes)
  let eJ : J0 ≃* J := subgroupOfEquivOfLe (show J ≤ D from le_sup_left)
  let eQ := QuotientGroup.congr (pCore 2 J0) (pCore 2 J) eJ (pCore_map_iso 2 eJ)
  refine {
    sqtk := (ChapterC.C27Source.source_join_input j.input).setup.sqtk
    fitting := ChapterC.C27Source.source_join_fitting j.input
    product := ?_
    component := (ChapterC.C27Source.source_join_input j.input).component.2
    radical := ChapterC.C27Source.msOddIndexRadical_join_from_source j.input
      (s.plane_msOddIndexRadical d J j)
    characteristic := ChapterC.C27Source.join_msCharacteristic_from_source j.input
    quotientEquiv := eQ.trans e }
  intro x
  have hg : J0 ⊔ Q.subgroupOf D = ⊤ := by
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  exact mem_sup_of_normal_left.mp (hg.ge (mem_top x))

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Representation.BinaryOffender
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- All hypotheses of the binary MS theorem hold on the literal join JQ. -/
theorem Context.component_has_binaryMS_input (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    Nonempty (ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple
      (J.subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2))
      (((L ⊔ T).pCoreIn 2).subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2))) := by
  obtain ⟨e⟩ := s.binary_linearThree_core_model d J j
  exact ⟨s.component_binaryMS_input d J j e⟩

/-- The escaping original centralizer supplies a genuine binary MS configuration. -/
theorem Context.exists_binaryMS_component (s : Context T L V) (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J : Subgroup G, Nonempty (LocalData T L d J) ∧
      Nonempty (ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple
        (J.subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2))
        (((L ⊔ T).pCoreIn 2).subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2))) := by
  obtain ⟨J,⟨j⟩⟩ := s.localExtraction d hout
  exact ⟨J,⟨j⟩,s.component_has_binaryMS_input d J j⟩

/-- The terminal row now needs only identification of the original residual. -/
theorem Context.linearThreeRow_of_residual (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (hr : J = (primeToResidual 3 (centralizer (d.A : Set G))).map
      (centralizer (d.A : Set G)).subtype) : Nonempty (LinearThreeRow T L d J) := by
  obtain ⟨i⟩ := s.component_has_binaryMS_input d J j
  exact ⟨⟨i,hr,s.component_marked_cubic d J j⟩⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
