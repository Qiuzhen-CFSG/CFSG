module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.OriginalSetup.Residual
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness.AmbientSpans
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.LocalSelection

/-!
# Original local setup for the extraspecial branch of 15.3.49

Starting with the actual orthogonal local datum, the original preceding
source hypotheses and the extraspecial alternative, this module constructs
the complete EarlierLocal record at Mc. The eligible family is based at
Y0T, with Y0 the literal centralizer residual. The Sylow supplement supplies
the centralizer containment required by 15.3.48 for every family member.

The original residual calculation bounds Omega₁(O₂(H)) by S. The faithful
commutator pairing from 15.3.48 then puts the large conjugate span in O₂(H),
and fusion makes that span elementary abelian. Thus the centered small span,
the large-span core containment, local characteristic two and every intrinsic
15.3.48 premise are available uniformly for the geometric assembly.

Source: Aschbacher--Smith, combined manuscript, 15.3.7,15.3.46,15.3.48 and
15.3.49(b)--(d), printed pp.1122 and 1141--1143.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.OriginalSetup
open ChapterA.Section05To06 OriginalSource ExtraspecialLocal
open ExtraspecialElimination ExtraspecialElimination.ContainedOffenderRoute
open ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement
variable {G : Type*} [Group G] [Finite G]

private theorem residualY_normalized (d : CharacteristicTwo.LocalData G) :
    (d.T : Subgroup G) ≤ normalizer (d.Y : Set G) :=
  d.sylow_le.trans ((normal_subgroupOf_iff_le_normalizer
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)).mp
      (residualY_normal d.M d.Mc))

/-- Every eligible overgroup has the actual extraspecial side condition of 15.3.48. -/
theorem centralizer_le_of_eligible (d : CharacteristicTwo.LocalData G)
    (H : Subgroup G) (hH : H ∈ outsideFamily (residual d) (d.T : Subgroup G) d.M) :
    d.Y ⊓ centralizer (d.V : Set G) ≤ H :=
  centralizer_le_intermediate d.Y d.V (residual d) H d.T
    (residualY_normalized d) (d.sylow_le.trans d.action.normalizes) rfl hH.1.2

/-- The uniform characteristic-two premise uses the actual Sylow overgroups in Mc. -/
theorem local_characteristic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (H : Subgroup G) (hTH : (d.T : Subgroup G) ≤ H) (hHMc : H ≤ d.Mc) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have hMc : d.Mc ∈ maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) :=
    hu ▸ Set.mem_singleton _
  exact Preamble.H_core_selfCentralizing d.T d.Mc H (hG.evenCharacteristic d.T) hMc.1 hTH hHMc

/-- Original 15.3.7 gives the literal centralizer factorization. -/
theorem centralizer_factorization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard) :
    ∀ x ∈ d.M ⊓ centralizer (d.Z : Set G),
      ∃ c ∈ d.M ⊓ centralizer (d.V : Set G), ∃ t ∈ (d.T : Subgroup G), c * t = x := by
  have hC := source_partner_eq hG d hempty hM hu hmany
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨_,_,hprod,_⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  intro x hx
  have hx' : x ∈ d.M ⊓ d.Mc := by simpa only [hC] using hx
  have hm : x ∈ ((d.M ⊓ centralizer (d.V : Set G) : Subgroup G) : Set G) *
      (d.T : Set G) := hprod ▸ hx'
  exact hm

/-- The centralizer partner is an actual member of the outside family based at Y0T. -/
theorem partner_eligible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard) :
    d.Mc ∈ outsideFamily (residual d) (d.T : Subgroup G) d.M := by
  have hMc : d.Mc ∈ maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) :=
    hu ▸ Set.mem_singleton _
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have hTH : (d.T : Subgroup G) ≤ d.Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans hMc.2
  have hRH : residual d ≤ d.Mc := (residual_le d).trans
    (inf_le_right.trans ((centralizer_le (le_conjugateSpanBy _ _)).trans hMc.2))
  exact ⟨⟨Chapter1.mem_H_of_isTwoLocal hMc.1.1,sup_le hRH hTH⟩,
    fun hh => hne (hMc.1.eq_of_le hM.1.1.1 hh)⟩

/-- The original extraspecial local calculation supplies theta and the needed omega bound. -/
theorem local_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (he : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (H : Subgroup G) (hTH : (d.T : Subgroup G) ≤ H) (hHMc : H ≤ d.Mc)
    (hCH : d.Y ⊓ centralizer (d.V : Set G) ≤ H) :
    residual d = theta (d.M ⊓ H) ∧ omegaOneAmbient (H.pCoreIn 2) ≤ d.S := by
  have hC := source_partner_eq hG d hempty hM hu hmany
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨hi,_,hp,_,_,hq,_⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have hf : ∀ x ∈ d.M ⊓ d.Mc,
      ∃ c ∈ d.M ⊓ centralizer (d.V : Set G), ∃ t ∈ (d.T : Subgroup G), c * t = x := by
    intro x hx
    have hm : x ∈ ((d.M ⊓ centralizer (d.V : Set G) : Subgroup G) : Set G) *
      (d.T : Set G) := hp ▸ hx
    exact hm
  obtain ⟨_,ht,_,_,_,_,_,_,_,_,_,ho⟩ := extraspecial_local_calculation
    d.M d.Mc H d.Y d.V d.T d.action rfl rfl hC (extraspecialCase d he)
    d.sylow_le hTH hHMc hCH hf hq hi
  exact ⟨ht,ho 1⟩

/-- Both actual spans satisfy 15.3.49(c),(d); all intrinsic 15.3.48 premises are discharged. -/
theorem local_spans
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    (he : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (H : Subgroup G) (hTH : (d.T : Subgroup G) ≤ H) (hHMc : H ≤ d.Mc)
    (hout : ¬ H ≤ d.M) (hCH : d.Y ⊓ centralizer (d.V : Set G) ≤ H) :
    localSpan d.ZS H ≤ (center (omegaOneAmbient (H.pCoreIn 2))).map
        (omegaOneAmbient (H.pCoreIn 2)).subtype ∧
      IsElementaryAbelian 2 (localSpan d.ZS H) ∧
      localSpan d.V H ≤ H.pCoreIn 2 ∧ IsElementaryAbelian 2 (localSpan d.V H) := by
  let : IsElementaryAbelian 2 d.V := Preamble.vector_elementary d.action
  let : IsElementaryAbelian 2 d.ZS := d.action.elementary_fixedPlane _
  have h := source_hypothesis hG d hempty hM hu hmany hfixed H hTH hHMc hout (fun _ => hCH)
  have hh := source_conclusions d H h
  have hC := source_partner_eq hG d hempty hM hu hmany
  have hAQ : d.ZS ≤ H.pCoreIn 2 := (le_conjugateSpanBy _ _).trans h.UH_le_QH
  have hQ : H.pCoreIn 2 ≤ (d.T : Subgroup G) := by
    rintro x ⟨x,hx,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (d.T.subtype hTH) hx
  have hN : normalizer (d.V : Set G) = d.M :=
    (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).symm
  have hw := OriginalCoordinates.fusion_bounds d.action (source_fusion_inputs hG d hM hfixed)
  exact FittingFaithfulness.ambient_extraspecial_spans_of_emptyLf_and_omega_bound
    d.T H d.V d.ZS d.S hTH ((source_seed_geometry d).1.trans hTH) h.plus_le_H
    (local_characteristic hG d hu H hTH hHMc) hempty hAQ inf_le_right
    (local_geometry hG d hempty hM hu hmany he H hTH hHMc hCH).2
    (source_seed_geometry d).2.1.le (hHMc.trans_eq hC)
    (d.action.card_centralInvolutions d.T d.sylow_le) hh.2.2.1 hh.2.2.2.2 hh.2.2.2.1
    (hQ.trans (d.sylow_le.trans d.action.normalizes))
    (fun g _ hg => hw.1 g (hg.trans_eq hN))

/-- Uniform 15.3.49(c),(d) on the literal eligible family, including the input core bound for F.9. -/
theorem local_conclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    (he : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (H : Subgroup G) (hH : H ∈ outsideFamily (residual d) (d.T : Subgroup G) d.M)
    (hHMc : H ≤ d.Mc) :
    localSpan d.ZS H ≤ (center (omegaOneAmbient (H.pCoreIn 2))).map
        (omegaOneAmbient (H.pCoreIn 2)).subtype ∧
      IsElementaryAbelian 2 (localSpan d.ZS H) ∧
      d.V ≤ H.pCoreIn 2 ∧ localSpan d.V H ≤ H.pCoreIn 2 ∧
      IsElementaryAbelian 2 (localSpan d.V H) := by
  obtain ⟨hc,heU,hVQ,heV⟩ := local_spans hG d hempty hM hu hmany hfixed he
    H (le_sup_right.trans hH.1.2) hHMc hH.2 (centralizer_le_of_eligible d H hH)
  exact ⟨hc,heU,(le_conjugateSpanBy _ _).trans hVQ,hVQ,heV⟩

/-- The original source data construct every field needed before minimal-local selection. -/
theorem earlierLocal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    (he : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) :
    EarlierLocal KnownSimple.IsKnownSimple d.M d.Y d.V (residual d) d.ZS d.Z d.Mc d.T := by
  let : IsElementaryAbelian 2 d.V := Preamble.vector_elementary d.action
  have hMc : d.Mc ∈ maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) :=
    hu ▸ Set.mem_singleton _
  have hel := partner_eligible hG d hempty hM hu hmany
  have hTH : (d.T : Subgroup G) ≤ d.Mc := le_sup_right.trans hel.1.2
  have hCH := centralizer_le_of_eligible d d.Mc hel
  have hc := source_partner_eq hG d hempty hM hu hmany
  have hf := OriginalCoordinates.fusion_bounds d.action (source_fusion_inputs hG d hM hfixed)
  refine {
    eligible := hel
    extraspecial := extraspecialCase d he
    residual := rfl
    sqtk := hG.twoLocal_sqtk hMc.1.1
    t_le_m := d.sylow_le
    v_le_t := (source_seed_geometry d).1
    y_le_m := Chapter14.SourcePreliminaries.sourceResidual_le _ _
    m_normalizes := d.action.normalizes
    t_normalizes_y := residualY_normalized d
    theta_eq := (local_geometry hG d hempty hM hu hmany he d.Mc hTH le_rfl hCH).1.symm
    normalizer_eq := residual_normalizer hG d hM he
    seed_le := inf_le_left
    line_le_seed := (source_seed_geometry d).2.1.le
    seed_normalizer := hf.2
    centralizes := hc.le
    elementary := (local_spans hG d hempty hM hu hmany hfixed he d.Mc hTH le_rfl hel.2 hCH).2.2.2
    centralizer_factorization := centralizer_factorization hG d hempty hM hu hmany
    kernel := ?_ }
  intro H hH hHU hCH
  exact (source_conclusions d H (source_hypothesis hG d hempty hM hu hmany hfixed
    H (le_sup_right.trans hH.1.2) hHU hH.2 (fun _ => hCH))).1

/-- Uniform intrinsic 15.3.48 in the exact family selected by the extraspecial consumer. -/
theorem uniform_48
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M) :
    ∀ H : Subgroup G, H ∈ outsideFamily (residual d) (d.T : Subgroup G) d.M → H ≤ d.Mc →
      localSpan (d.ZS.subgroupOf H) ⊤ ≤ pCore 2 H ∧
      (frattini (localSpan (d.ZS.subgroupOf H) ⊤)).map
        (localSpan (d.ZS.subgroupOf H) ⊤).subtype ≤ d.Z.subgroupOf H ∧
      (∀ x : H, (∀ u ∈ localSpan (d.ZS.subgroupOf H) ⊤,
        ⁅u,x⁆ ∈ d.Z.subgroupOf H) ↔ x ∈ pCore 2 H) ∧
      ⁅localSpan d.ZS H, localTwoCore H⁆ ≤ d.Z := by
  intro H hH hHU
  exact (source_conclusions d H (source_hypothesis hG d hempty hM hu hmany hfixed
    H (le_sup_right.trans hH.1.2) hHU hH.2
    (fun _ => centralizer_le_of_eligible d H hH))).2

/-- Uniform local characteristic two for the same family. -/
theorem uniform_characteristic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc}) :
    ∀ H : Subgroup G, H ∈ outsideFamily (residual d) (d.T : Subgroup G) d.M → H ≤ d.Mc →
      centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  intro H hH hHU
  exact local_characteristic hG d hu H (le_sup_right.trans hH.1.2) hHU

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.OriginalSetup
