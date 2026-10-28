module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceClassifications
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Quasisimple
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.MarkedClassification

/-!
# Native strict-ratio deductions for the terminal A₅ argument

The proved marked B.4 classification excludes an involution moving at most
two dimensions on each terminal exceptional component. Rank-nullity supplies
such an involution in degree at most four, proving the exact constituent-degree
premise used in the original star-quotient action without universal B.4 inputs.
For PSL₃(4), the independent linear source recognition at quadratic ratio two
forces a natural SL₃ model; the existing center and group comparisons exclude it.

These deductions preserve the literal component and quotient actions. The
remaining M₂₃ and J₂ strict bounds are separate source-module calculations.
Source: Aschbacher–Smith B.4.2–5, K.3 and terminal §13.6, pp.86–87,455–456,935.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.NativeStrictBound
open StrictBound Section08
universe u v

private theorem exceptionalModel_comap {L M : Type*} [Group L] [Group M]
    (e : L ≃* M) (hm : ExceptionalModel M) : ExceptionalModel L := by
  unfold ExceptionalModel at hm ⊢
  rcases hm with hm | hm | hm
  all_goals obtain ⟨f⟩ := hm
  · exact .inl ⟨e.trans f⟩
  · exact .inr (.inl ⟨e.trans f⟩)
  · exact .inr (.inr ⟨e.trans f⟩)

theorem not_small_involution_of_exceptional
    {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V)
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hz : center (generalizedFitting D) = ⊥)
    (hm : ExceptionalModel (generalizedFitting D))
    (hq : quadraticRatio ρ ≤ 2) (t : D) (ht : orderOf t = 2)
    (hd : fixedCodim ρ (zpowers t) ≤ 2) : False := by
  have hs : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting D) :=
    ⟨hyp.sqtk, rfl, hyp.quasisimple, hyp.faithful, hyp.irreducible,
      (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩
  have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank] at hd
    exact hd
  have hc : Classifications.ClassicalCompetitor (generalizedFitting D) ∨
      Classifications.FixedCompetitor (generalizedFitting D) := by
    rcases ChapterB.SmallRatioClassification.actionCase_of_small_involution hs hq t ht hr with h | h
    · exact Classifications.competitors_of_B42 ρ hz
        (SourceClassifications.actionCase_of_center_eq_bot ρ hz
          (Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.SourceB5.irreducible h))
    · exact Classifications.competitors_of_table ρ hz h hq
  rcases hc with hc | hc
  · exact Classifications.not_classicalCompetitor_of_exceptional hm hc
  · exact Classifications.not_fixedCompetitor_of_exceptional hm hc

theorem finrank_gt_four_of_exceptional
    {L : Type u} [Group L] [Finite L] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V)
    (hsq : IsSQTK KnownSimple.IsKnownSimple L) (hf : Function.Injective ρ)
    (hL : IsQuasisimple L) (hi : ρ.IsIrreducible) (hz : center L = ⊥)
    (hm : ExceptionalModel L) (t : L) (ht : orderOf t = 2) :
    4 < Module.finrank (ZMod 2) V := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := hL
  have hfit : generalizedFitting L = ⊤ := top_unique
    (component_le_generalizedFitting L ⊤ ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  let e : generalizedFitting L ≃* L := (MulEquiv.subgroupCongr hfit).trans topEquiv
  have hz' : center (generalizedFitting L) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (centerCongr e).toEquiv, hz]
    exact Subgroup.card_bot
  by_contra! hdim
  have hq := quadraticRatio_le_two_of_finrank_le_four ρ t ht hdim
  have hd := (involution_actor_rank_and_fixedCodim ρ t ht).2.2.2
  exact not_small_involution_of_exceptional ρ
    (Classifications.b4Hypotheses_intrinsic ρ hsq hf hL hi) hz'
    (exceptionalModel_comap e hm) hq t ht (by omega)

theorem quadraticRatio_gt_two_of_linearThreeFour
    {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V)
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hz : center (generalizedFitting D) = ⊥)
    (e : generalizedFitting D ≃* Components.L3Four) :
    2 < quadraticRatio ρ := by
  by_contra! hq
  have hquot : ClassicalGroup.IsPSL
      (generalizedFitting D ⧸ center (generalizedFitting D)) 3 (2 ^ 2) := by
    refine ⟨Components.F4, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
    · exact GaloisField.card 2 2 (by decide)
    · exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e
  have h := ChapterK.Linear.Recognition.SourceQuadratic.actionCase_of_quadratic_le_two
    ⟨inferInstance, inferInstance, hyp.sqtk, rfl, hyp.quasisimple,
      hyp.faithful, hyp.irreducible, (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩
    2 (by decide) hquot hq
  rcases Classifications.competitors_of_B42 ρ hz
      (SourceClassifications.actionCase_of_center_eq_bot ρ hz
          (Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.SourceB5.irreducible h)) with hc | hc
  · exact Classifications.not_classicalCompetitor_of_exceptional (Or.inl ⟨e⟩) hc
  · exact Classifications.not_fixedCompetitor_of_exceptional (Or.inl ⟨e⟩) hc

/-- The literal constituent-degree premise used by `component_action_of_source`.
The complete source component conclusion supplies the involution and model,
and SQTK descends from the actual star quotient. No B.4 classification is an input. -/
theorem component_constituent_degree_gt_four
    {G : Type u} [Group G] [Finite G]
    (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hn : H ≤ normalizer (V₁ : Set G))
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
    (S : Subgroup H) (hs : Components.Conclusion S)
    (hsqtk : IsSQTK KnownSimple.IsKnownSimple (Source.Hstar H))
    (U : Subrepresentation (starRepresentation H V₃ V₁ hn hk))
    (N : Subrepresentation U.toRepresentation)
    (I : Subrepresentation
      (N.quotientRepresentation.comp
        (Source.starImage H (terminalResidual H)).subtype))
    (hf : Function.Injective I.toRepresentation)
    (hi : Representation.IsIrreducible I.toRepresentation) :
    4 < Module.finrank (ZMod 2) I.toSubmodule := by
  let : Finite (U.toSubmodule ⧸ N.toSubmodule) :=
    Finite.of_surjective _ N.toSubmodule.mkQ_surjective
  obtain ⟨t, ht⟩ := residual_involution_of_source H S hs
  exact finrank_gt_four_of_exceptional I.toRepresentation
    (hsqtk.subgroup _) hf (residual_quasisimple_of_source H S hs) hi
    (residual_center_of_source H S hs) (residual_model_of_source H S hs).2 t ht

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.NativeStrictBound
