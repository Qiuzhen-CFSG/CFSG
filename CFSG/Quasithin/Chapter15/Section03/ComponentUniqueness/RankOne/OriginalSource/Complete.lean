module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OriginalSource.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OriginalSource.Models
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OriginalSource.Geometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OriginalSource.NonNormal
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.OriginalModels

/-!
# Original marked rank-one uniqueness contradiction

The actual marked ordinary component supplies the full 1.1.5 model list.
For a fixed Sylow orbit that list gives inner action; for a moving orbit
the literal cubic residual gives inner action. The actual plane reduction
then contradicts every marked model. Only the preceding characteristic-two
exclusion remains for its independent original-source producer.

Source: Aschbacher--Smith 15.3.25, 15.3.33 and 15.3.43, pp.1130--1140.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankOne
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Actual marked source classification gives inner action in a singleton
Sylow orbit; the original cubic residual gives it in a moving orbit. -/
theorem inner_of_original_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.Hplus) (h : ReductionSourceInputs d I L)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {z : G} (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) d.M z) :
    d.Yplus ≤ L ⊔ centralizer (L : Set G) := by
  by_cases hn : d.S ≤ normalizer (L : Set G)
  · obtain ⟨localSetup, planes⟩ := original_local_geometry d hI h hshadow
    obtain ⟨α, _, hm⟩ := h33.model_action
    let e := subgroupOfEquivOfLe h.component_le
    have horbit : L = localSpan L d.S :=
      (le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy L d.S)).symm
    exact DiagonalExclusion.OriginalModels.inner_of_modelAction115 d localSetup planes
      horbit (hm.of_mulEquiv e.symm)
  · exact inner_of_original_nonnormal hG d hI h hshadow hn

/-- The actual15.3.43 source consumer, retaining only the preceding15.3.25
characteristic-two exclusion. Component selection, marked classification,
inner action, plane placement and every model contradiction are derived. -/
theorem source_not_symmetricThreeShadow_of_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h25 : SymmetricThreeShadow d.Yplus d.S →
      ∀ A ∈ d.Hplus, generalizedFitting A ≠ pCore 2 A)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) :
    ¬ SymmetricThreeShadow d.Yplus d.S := by
  intro hshadow
  obtain ⟨L, z, h, h33⟩ := exists_reduction_inputs_from_original
    hG d hempty hM hu hmany hshadow (h25 hshadow) hI.1
  have hi := inner_of_original_component hG d hI.1 h hshadow h33
  exact not_marked_component_of_original_configuration
    (reducedConfiguration_of_original_inner d hI h hshadow hi) h33

end CFSG.Quasithin.Chapter15.Section03.RankOne
