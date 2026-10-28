module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.DistanceFourExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.SmallSylow

/-!
# Degree-four binary exclusion from the actual larger-distance geometry

The natural-dual residual pair supplied by original 15.3.24 has nonabelian
commutator core and critical distance greater than four. Its marked Sylow
subgroup has elementary center of order four by original 15.3.8. Consequently
the included four-group furnished by the larger-distance argument violates
MS3 once prescribed replacement and fixation by the original two-core hold.

The final theorem constructs the original component and span premises before
applying this argument to the literal selected residual pair. Prescribed
replacement and the original two-core action are the two remaining shared
source inputs; centrality in the characteristic replacement alone does not
supply the latter.

Source: Aschbacher–Smith, 15.3.8 and 15.3.24, printed pp. 1123, 1129–1130;
MS93, (4.4), through the shared Chapter C larger-distance consumer.
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

/-- Transport the original central-omega four-group to the same residual Sylow. -/
theorem source_binaryFour_residual_omega_card (h : NaturalDual d L) (x : Space 4)
    (P : Sylow 2 (residualOvergroup h x))
    (hmark : (P : Subgroup (residualOvergroup h x)).map
      (residualOvergroup h x).subtype = d.S) :
    Nat.card (Stellmacher.omegaOneCenterAmbient (P : Subgroup (residualOvergroup h x))) = 4 := by
  have hmap : (Stellmacher.omegaOneCenterAmbient (P : Subgroup (residualOvergroup h x))).map
      (residualOvergroup h x).subtype = centralOmegaIn d.S := by
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective
      (residualOvergroup h x).subtype (residualOvergroup h x).subtype_injective,hmark]
    rfl
  rw [← card_map_of_injective (f := (residualOvergroup h x).subtype)
    (residualOvergroup h x).subtype_injective,hmap]
  have h8 := source_lemma_15_3_8 d.T d.action d.sylow_le 1
  rw [← h8.1]
  exact d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1

/-- On the literal natural-dual residual, the two exact remaining MS93
geometry inputs suffice; no full classification witness is required. -/
theorem source_binaryFour_false_of_replacement_and_core_action
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (input : Input KnownSimple.IsKnownSimple (residualComponent h x) (sylowPart h x))
    (t : InputSetup input)
    (replacement : ∀ {a a'} (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p)
    (hc : t.reducedCentralFour ≤ centralizer
      (pCore 2 (residualOvergroup h x) : Set (residualOvergroup h x))) : False := by
  have hnon := binaryInput_core_nonabelian_of_theta h hx hS hθ input
  have hb := binaryInput_distance_gt_four_of_theta h hx hS hθ input t
  obtain ⟨common⟩ := t.commonFacts hnon
  obtain ⟨P,hmark⟩ := residualOvergroup_sylow h x (hθ ▸ theta_le I) hS
  have hR : sylowPart h x = (P : Subgroup (residualOvergroup h x)) := by
    apply map_injective (residualOvergroup h x).subtype_injective
    exact (map_subgroupOf_eq_of_le (show d.S ≤ residualOvergroup h x from le_sup_right)).trans
      hmark.symm
  exact t.false_of_large_distance_of_replacement_and_core_action P hR
    (source_binaryFour_residual_omega_card h x P hmark).le common hb replacement hc

/-- The full original source24 context reduces to prescribed critical-path
replacement and fixation of the included four-group by the original two-core.
Both premises are on the actual selected natural-dual residual input. -/
theorem source_lemma_15_3_24_four_of_replacement_and_core_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(4,ZMod 2))
    (geometry : ∀ (h : NaturalDual d c.L) (x : Space 4), x ≠ 0 →
      ∀ (input : Input KnownSimple.IsKnownSimple (residualComponent h x) (sylowPart h x)),
      ∃ t : InputSetup input,
        (∀ {a a'} (p : CriticalPath t.reduction.radical t.geometry a a'),
          HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) ∧
        t.reducedCentralFour ≤ centralizer
          (pCore 2 (residualOvergroup h x) : Set (residualOvergroup h x))) : False := by
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
  intro h x hx input P hP
  obtain ⟨t,hreplacement,hcore⟩ := geometry h x hx input
  exact (source_binaryFour_false_of_replacement_and_core_action h hx h11.sylow
    hc.component_eq_theta input t hreplacement hcore).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
