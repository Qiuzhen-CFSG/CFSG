module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentEscapeAt
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.Components.Selection
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ReducedDetection
public import CFSG.Quasithin.Chapter13.Section01.LocalModelRigidity
public import Theory.GroupTheory.ReducedNormal.SylowCenter
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.SpecificGroups.PSL3Two.Parabolics.SolvableOvergroups

/-!
# An overcomponent escaping the original point is faithful

The original point has order two and is central in the Sylow subgroup.
Its movement by an actual local component detects that component's
intrinsic signalizer module. Earlier 14.3.4 then gives A₅ or PSL₃(2), whose
proper full-Sylow overgroups are solvable. Comparable local components
therefore coincide by 13.1.2(5).
Source: Aschbacher–Smith 14.7.46, printed p.1063.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Escape from the actual point stabilizer detects the original intrinsic module. -/
theorem local_component_outside_point_faithful_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    {C : Subgroup G} (hC : C ∈ Chapter1.L G (T : Subgroup G))
    (hout : ¬ C ≤ F.H) : IsFaithfulSignalizerType C := by
  let := h.chosen.elementary
  have hmove : ¬ C ≤ centralizer (F.Vi 1 : Set G) := fun hc =>
    hout (hc.trans (Subgroup.centralizer_le_normalizer _))
  let J := C ⊔ (T : Subgroup G)
  let S : Sylow 2 J := T.subtype le_sup_right
  have hchar : centralizer (pCore 2 J : Set J) ≤ pCore 2 J :=
    Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (d.qtke.evenCharacteristic T)
        ⟨hC.2.2, show (T : Subgroup G) ≤ J from le_sup_right⟩)
  have hZT : F.Vi 1 ≤ (T : Subgroup G) := (F.le_seed 1).trans h.chosen.le_sylow
  have hTZ : (T : Subgroup G) ≤ centralizer (F.Vi 1 : Set G) :=
    (F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  have hZR : (F.Vi 1).subgroupOf J ≤ reducedTwoSubgroup J := by
    intro z hz
    apply sylow_omegaCenter_le_reduced S hchar
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hZT hz, ?_, ?_⟩
    · intro t ht
      exact Subtype.ext ((hTZ ht z hz).symm)
    · exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (z : G) (F.le_seed 1 hz))
  have hnon : ⁅reducedTwoSubgroup J, C.subgroupOf J⁆ ≠ ⊥ := by
    intro he
    apply hmove
    intro c hc z hz
    let zJ : J := ⟨z, (show (T : Subgroup G) ≤ J from le_sup_right) (hZT hz)⟩
    let cJ : J := ⟨c, (show C ≤ J from le_sup_left) hc⟩
    exact (congrArg Subtype.val
      (commutator_eq_bot_iff_le_centralizer.mp he (hZR (show zJ ∈ (F.Vi 1).subgroupOf J from hz))
        cJ hc)).symm
  exact ⟨Chapter1.Section02.Adequate.mem_L_isSignalizerType T
    (d.qtke.evenCharacteristic T) hC,
    Chapter3.RadicalCentralization.intrinsicModule_ne_bot_of_reduced_action
      C J le_sup_left hC.1.subnormal (Chapter1.Section02.Adequate.mem_L_isPPerfect hC) hnon⟩

/-- An escaping local overcomponent cannot properly contain another original
local component. Both small models come from the earlier faithful classifier. -/
theorem local_overcomponent_eq_of_outside_point_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    {C K : Subgroup G} (hC : C ∈ Chapter1.L G (T : Subgroup G))
    (hK : K ∈ Chapter1.L G (T : Subgroup G)) (hKC : K ≤ C)
    (hout : ¬ C ≤ F.H) : K = C := by
  have hf := local_component_outside_point_faithful_at d h hC hout
  have hm := (faithful C hC hf).1
  have hs : SolvableSylowOvergroups (C ⧸ pCore 2 C) := by
    rcases hm with he | he
    · obtain ⟨e⟩ := he
      intro S P _ hp
      exact alternatingGroup.isSolvable_subgroup_of_equiv_five e P hp
    · obtain ⟨e⟩ := he
      exact SolvableSylowOvergroups.of_equiv e Matrix.PSL3Two.solvableSylowOvergroups
  exact Chapter13.Section01.LocalModelRigidity.local_eq_of_solvableSylowOvergroups
    hC hK hKC hs

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
