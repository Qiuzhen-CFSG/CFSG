module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Source
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleSections
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.RankOne

/-!
# No strong FF modules for the exchanged field-four actor

B.1.5(4) normalizes both actual components under a best offender. The
faithful fixed-core restriction reduces to a single PSL₂(4) generalized
Fitting subgroup. B.1.5(3) stabilizes its irreducible section, so the proved
rank-one recognition applies to the literal action. Its natural ratio is
one and its two Hermitian endpoint ratios are one or two, contradicting
strong offending. No universal B.4.2 or module-classification callback is
assumed. The source actor construction and section application are separate.

Source: Aschbacher–Smith, 13.8.16(1), printed p.952; B.1.5(3–4),
B.4.2(1,5), and K.3.1, printed pp.68–70, 86–87 and 453–454.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open F918Sections.NoStrong IrreducibleReduction
universe u v

private theorem strong_fieldFour_action_false
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (a : StrongPSLTwoAction.{u,v,0} KnownSimple.IsKnownSimple F) : False := by
  let : FiniteDimensional (ZMod 2) a.Space := Module.Finite.of_finite
  obtain ⟨A, hA⟩ := a.strong
  have hff : IsFFModule a.representation := ⟨A, hA.1, hA.2.le⟩
  have h := ChapterB.SourceClassification.source_hypotheses
    a.hypotheses.sqtk rfl a.hypotheses.quasisimple a.hypotheses.faithful
    a.hypotheses.irreducible hff
  have hz : center (generalizedFitting a.Actor) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr a.componentEquiv ⟨x, hx⟩).property
    change a.componentEquiv x ∈ center PSL(2,F) at hh
    rw [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] at hh
    exact mem_bot.mpr (a.componentEquiv.injective (hh.trans a.componentEquiv.map_one.symm))
  have hm : ClassicalGroup.IsPSL
      ((generalizedFitting a.Actor) ⧸ center (generalizedFitting a.Actor)) 2 (2 ^ 2) :=
    ⟨F, inferInstance, inferInstance, hF,
      ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans
        a.componentEquiv⟩⟩
  have hr := (isStrongFFModule_iff_quadraticRatio_lt_one a.representation).mp a.strong
  obtain ⟨E, hE, hfin, hchar, hcard, e, hdim, halt⟩ := h.psl2_case (by decide) hm
  rcases halt with ⟨_, _, M, hratio, _⟩ | ⟨s, hs, _, hpos, _, _, M, _, _, hsmall⟩
  · rw [hratio] at hr
    exact lt_irrefl _ hr
  · have hs1 : s = 1 := by omega
    rcases hsmall hs1 with ⟨_, _, hratio, _⟩ | ⟨_, _, hratio, _⟩
    · rw [hratio] at hr
      norm_num at hr
    · rw [hratio] at hr
      exact lt_irrefl _ hr

/-- The field-four exchanged actor has no strong faithful binary module.
B.1.5 supplies component normalization and constituent stabilization;
the proved rank-one theorem supplies the exact ratios. -/
theorem exchanged_not_strong
    {D : Type u} [Group D] [Finite D]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (d : ExchangedActor KnownSimple.IsKnownSimple D F 2)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ) :
    ¬ IsStrongFFModule ρ := by
  intro hs
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨a⟩ := preaction_of_component_normalization d ρ hf hs (by
    intro A hA
    exact ⟨ChapterB.source_lemma_B_1_5_4 ρ hf hA d.component_isComponent,
      ChapterB.source_lemma_B_1_5_4 ρ hf hA d.second_isComponent⟩)
  obtain ⟨b⟩ := a.action_of_stabilization (by
    intro A hA I hI
    have hc := a.stabilization_hypotheses hA.1.1
    exact ChapterB.source_lemma_B_1_5_3 a.representation a.faithful hA hc.1 hc.2.2 hc.2.1 hI)
  exact strong_fieldFour_action_false d.field_card b

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
