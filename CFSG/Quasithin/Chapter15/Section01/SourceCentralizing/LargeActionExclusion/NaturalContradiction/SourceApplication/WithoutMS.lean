module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.SourceTheorem
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.SourceApplication
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion

/-!
# Applying original 15.1.29 without a universal MS premise

Apply the completed parabolic contradiction to the literal chosen module.
For an exchanged linear component, original 15.1.28 constructs the natural
marking on an actual element of T outside S, discharging the recognition
premise of 15.1.29. The last adapter connects this contradiction to the
original large action. Its earlier component-selection premise remains with
the 15.1.15 assembly owner; no parabolic or MS callback remains.

Source: Aschbacher--Smith, 15.1.28--29 and the conclusion of 15.1.15,
printed pp.1103--1104.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterA.Section05To06 Section03 Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]

/-- Literal chosen-module application of 15.1.29, with all parabolic and
MS inputs discharged on the original component. -/
theorem PreparedChosenModule.source_natural_parabolic_contradiction_without_ms
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (d : CaseIComponentData T M Mc V) (hlinear : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnatural : d.HasNaturalMovedModule t) : False :=
  CaseIComponentData.false_of_natural_moved_module_without_ms
    hG hempty hM hJ hu h hfull hlinear t ht htS hnatural

/-- Combine original 15.1.28 and 15.1.29 on the same selected component
and actual moving element. Only the earlier exchanged linear recognition
is needed from the component-reduction owner. -/
theorem CaseIComponentData.HasExchangedLinearSource.false_without_ms
    {T : Sylow 2 G} {M Mc V : Subgroup G} {d : CaseIComponentData T M Mc V}
    (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hfull : V = localModule T M)
    (h : PreparedChosenModule T M V) : False := by
  obtain ⟨t,ht,htS⟩ := s.1.exchange_exists
  exact h.source_natural_parabolic_contradiction_without_ms hG T hempty hM hJ hu
    hfull d s t ht htS
    (s.natural_moved_module hG hempty hM hmany hJ hu hne hfull h t ht htS)

/-- The literal large-action consumer after earlier component recognition.
The 15.1.15 assembly owner supplies that independent recognition implication;
this application requires no local construction or universal MS hypothesis. -/
theorem PreparedChosenModule.not_large_source_of_linear_recognition_without_ms
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hlinear : (letI := h.elementary; LargeSourceAction T M V h.normalized) →
      ∃ d : CaseIComponentData T M Mc V, d.HasExchangedLinearSource) :
    letI := h.elementary; ¬ LargeSourceAction T M V h.normalized := by
  intro ha
  obtain ⟨d,hs⟩ := hlinear ha
  exact hs.false_without_ms hG hempty hM hmany hJ hu hne hfull h

end CFSG.Quasithin.Chapter15.Section01
