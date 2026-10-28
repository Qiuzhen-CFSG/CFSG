module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.CoreMovement
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.Intersection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.OriginalGeometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.OriginalFusion
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.ClassifiedSections.Source
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.NaturalDualRank
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SpanSplittingSource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Complete

/-!
# Original 15.3.49 on the fixed-plane normalizer

The original local hypotheses and 15.3.45 construct the extraspecial
EarlierLocal data and the finite family of actual F.9 endpoints. The
contained-offender contradiction uses the proved appendix classification,
component orbit, splitting and natural-plus-dual rank inputs. This excludes
the extraspecial residual alternative. Its ordinary alternative identifies
the actual centralizer kernel and removes every factor of three from the
fixed-plane normalizer.

Only the original 15.3.45 fixed-line centralizer bound remains an earlier
source input; the parent assembly supplies it for this same local datum.
Source: Aschbacher--Smith, 15.3.49(3)--(5), combined manuscript
(1 March 2004), printed pp.1142--1145.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49
open ExtraspecialElimination ContainedOffenderRoute OriginalSetup OriginalSource
open ComponentReduction.ModelReduction.BinaryModels
open ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine original local hypotheses exclude the extraspecial residual
alternative, including the exact F.9 geometry and all appendix inputs. -/
theorem not_extraspecial_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M) :
    ¬ ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action := by
  intro he
  classical
  let : IsElementaryAbelian 2 d.V := Preamble.vector_elementary d.action
  let e := earlierLocal hG d hempty hM hu hmany hfixed he
  let : IsElementaryAbelian 2 (localSpan d.V d.Mc) := e.elementary
  let o := OriginalCoordinates.quadraticAction d.action
  let f := source_fusion_inputs hG d hM hfixed
  have hp := OriginalCoordinates.plane_definite d.action 1
  have ht := Geometry.normalizer_test_of_earlier_inputs o f hp
  have hc := Geometry.intersecting_conjugates_commute_of_earlier_inputs o f hp
    (source_partner_eq hG d hempty hM hu hmany)
  let valid (H : Subgroup G) := H ∈ outsideFamily (residual d) (d.T : Subgroup G) d.M ∧ H ≤ d.Mc
  let hyp (H : Subgroup G) (hv : valid H) : (sourceSetup d H).Hypothesis :=
    source_hypothesis hG d hempty hM hu hmany hfixed H
      (le_sup_right.trans hv.1.1.2) hv.2 hv.1.2
      (fun _ => centralizer_le_of_eligible d H hv.1)
  let ι (H : Subgroup G) := if hv : valid H then (hyp H hv).CriticalEndpoint else PUnit
  have (H : Subgroup G) : Finite (ι H) := by
    by_cases hv : valid H
    · dsimp only [ι]
      rw [dif_pos hv]
      infer_instance
    · dsimp only [ι]
      rw [dif_neg hv]
      infer_instance
  have hgeometry : ∀ H : Subgroup G,
      H ∈ outsideFamily (residual d) (d.T : Subgroup G) d.M →
      (hHU : H ≤ d.Mc) →
      let := e.elementary_seed H hHU
      let := e.elementary_span H hHU
      Nonempty (GeometricFamily (ι H) d.Y (d.T : Subgroup G) H d.V d.ZS d.Z) := by
    intro H hH hHU
    let := e.elementary_seed H hHU
    let := e.elementary_span H hHU
    have hv : valid H := ⟨hH,hHU⟩
    obtain ⟨hcenter,_,hcore,_,_⟩ := local_conclusions hG d hempty hM hu hmany hfixed he H hH hHU
    let : IsElementaryAbelian 2 (sourceSetup d H).UH := by
      change IsElementaryAbelian 2 (localSpan d.ZS H)
      infer_instance
    let : IsElementaryAbelian 2 (sourceSetup d H).VH := by
      change IsElementaryAbelian 2 (localSpan d.V H)
      infer_instance
    have hg := geometricFamily_of_original (hyp H hv) (e.localInput H hH hHU).action
      hcenter ht hcore hc
    exact (by simpa only [ι, dif_pos hv, sourceSetup] using (Nonempty.intro hg))
  have h46 := lemma_15_3_46_of_earlier_inputs o f hp
  apply EarlierLocal.false_of_earlier_of_naturalDualRank d.T d.M d.Y (residual d)
    d.ZS d.Mc d.action o 1 e rfl (source_seed_commutator d) hempty
    (fun W hWV hW => not_not.mp (fun hN => hW (h46.2.1.2 W hWV hN)))
    (uniform_characteristic hG d hu)
    (uniform_48 hG d hempty hM hu hmany hfixed) ι hgeometry
    SourceB5.classification.general ReducedModels.earlierComponentSections_knownSimple
    OrbitClosure.earlierOrbitAlternative_knownSimple SourceB5.classification.quasisimple
    CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.sourceB214Splitting

/-- The original ordinary residual kernel, with the extraspecial branch discharged. -/
theorem ordinary_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M) :
    ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V := by
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have hc := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne).2.2.2.2.2.2
  exact hc.resolve_right (not_extraspecial_from_original hG d hempty hM hu hmany hfixed)

/-- Original 15.3.49(4) on every intersection with a subgroup of Mc. -/
theorem intersection_three_prime_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    {H : Subgroup G} (hHMc : H ≤ d.Mc) :
    Nat.Coprime 3 (Nat.card (d.M ⊓ H : Subgroup G)) := by
  have ho := ordinary_from_original hG d hempty hM hu hmany hfixed
  have hc := ExtraspecialLocal.centralizer_three_prime_of_ordinary d.M d.Y d.V ho.2.2 ho.1.symm
  exact ExtraspecialLocal.three_prime_of_residual_bound (d.M ⊓ H) d.M d.V inf_le_left hc
    (intersection_residual_centralizes_from_original hG d hempty hM hu hmany hHMc)

/-- Original 15.3.49(5) on the literal fixed-plane normalizer, with no
ordinary-kernel or extraspecial-exclusion premise. -/
theorem normalizer_three_prime_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M) :
    Nat.Coprime 3 (Nat.card (normalizer (d.ZS : Set G))) := by
  let : IsElementaryAbelian 2 d.V := Preamble.vector_elementary d.action
  have ho := ordinary_from_original hG d hempty hM hu hmany hfixed
  have hc := ExtraspecialLocal.centralizer_three_prime_of_ordinary d.M d.Y d.V ho.2.2 ho.1.symm
  have hN := (OriginalCoordinates.fusion_bounds d.action
    (source_fusion_inputs hG d hM hfixed)).2
  exact (ExtraspecialLocal.NormalizerAction.lemma_15_3_49_5_of_centralizer_three_prime
    d.T d.sylow_le d.action 1 hN hc).2

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49
