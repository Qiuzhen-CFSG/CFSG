module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryFourGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.LargeDistanceExclusion

/-!
# Degree-four source exclusion from prescribed replacement alone

The actual natural-plus-dual residual has neither an abelian core nor
critical distance four. At larger distance, prescribed replacement supplies
the earlier MS93 core layers. The literal natural summand then has displacement
in its central point line, so the large-core small-displacement theorem gives
the contradiction. The original two-core action on the replacement's fixed
factor is no longer a premise.

The final theorem constructs the original theta component and elementary span
before applying this argument to the selected source24 residual. Prescribed
critical-path replacement remains the independent earlier source obligation.

Source: Aschbacher–Smith 15.3.24, printed pp.1129–1130; MS93, (4.4)–(4.5).
-/

public section
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearFourFive NaturalDualParabolic NaturalDualParabolic.Realization
open ChapterC ChapterC.BinaryMS ChapterC.BinaryMS.MS93
open ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalData G} {L I : Subgroup G}

/-- On the literal source24 residual, all later action premises are discharged;
only the earlier critical-path replacement theorem remains. -/
theorem source_binaryFour_false_of_replacement
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (input : Input KnownSimple.IsKnownSimple (residualComponent h x) (sylowPart h x))
    (replacement : ∀ (t : InputSetup input),
      CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) :
    False := by
  have hnon := binaryInput_core_nonabelian_of_theta h hx hS hθ input
  obtain ⟨t⟩ := exists_setup input hnon
  obtain ⟨common⟩ := t.commonFacts hnon
  have hb := binaryInput_distance_gt_four_of_theta h hx hS hθ input t
  exact binaryInput_false_of_large h hx
    ((spanCommutator_le_componentCore_of_theta hS hθ).trans (componentCore_le_pointCore h x))
    ((Chapter1.isSylowIn_iff.mp hS).2.1.trans (normalizes_of_eq_theta hθ))
    input t common (Source44.SourceEarlier.earlier common hb (replacement t common hb))

/-- Original 15.3.24 in degree four, with the earlier replacement theorem as
its sole binary source input. Fixed central layers of the original span remain. -/
theorem source_lemma_15_3_24_four_of_replacement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(4,ZMod 2))
    (replacement : ∀ (h : NaturalDual d c.L) (x : Space 4), x ≠ 0 →
      ∀ (input : Input KnownSimple.IsKnownSimple (residualComponent h x) (sylowPart h x))
      (t : InputSetup input), CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) :
    False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hc := source_binary_component_conclusions hG d hempty hM hu hmany
    hI htwo hf c (Or.inl rfl) e
  have hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) := htwo.2.2.2.2.1
  have hW : d.componentSpan c.L ≤ c.L ⊔ d.R := by
    have hh := span_le_overgroup d c.L hR
    simpa only [overgroup,sup_eq_left.mpr (hc.yplus_le.trans le_sup_left)] using hh
  let _ := hc.span_reduced.elementary
  let _ : IsElementaryAbelian 2 (d.componentSpan c.L) :=
    IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hW).toMonoidHom
      (subgroupOfEquivOfLe hW).surjective
  apply source_lemma_15_3_24_four_of_binary_ms hG d hempty hM hu hmany hI htwo hf c e
  intro h x hx input _P _hP
  exact (source_binaryFour_false_of_replacement h hx h11.sylow hc.component_eq_theta
    input (replacement h x hx input)).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
