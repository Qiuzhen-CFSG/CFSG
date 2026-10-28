module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ContextKnownSimple

/-!
# The bounded original A₅ action before component uniqueness

The known-simple source geometry constructs the literal faithful action of
C_G(V₁)/O₂(C_G(V₁)) on U_H/V₁ with quadratic ratio at most two. All F.9 inputs
are supplied by the original marked context, and equality transport preserves
the selected line, the source module, and the exact quotient kernel.

This input is shared by the Suzuki-isolation and J₄ terminal contradictions;
it does not require a component conclusion or source5.2.3.
Source: Aschbacher–Smith13.5.7, F.9.16(3), and13.6, printed p.935.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Ratio Section05.A5Source CentralizerReduction CentralizerReduction.A5Module Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The original singular centralizer has its bounded faithful binary action,
without a component conclusion or an earlier5.2.3 input. -/
theorem source_bounded_faithful_action_of_context
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) :
    ∃ hU : IsElementaryAbelian 2 (Source.UH (centralizer (V₁ : Set G)) V₃),
      letI := hU
      ∃ (hn : centralizer (V₁ : Set G) ≤ normalizer (V₁ : Set G))
        (hk : commutatorPreimage (centralizer (V₁ : Set G))
          (Source.UH (centralizer (V₁ : Set G)) V₃) V₁ =
            Source.QH (centralizer (V₁ : Set G))),
        Function.Injective (starRepresentation (centralizer (V₁ : Set G)) V₃ V₁ hn hk) ∧
        Representation.BinaryOffender.quadraticRatio
          (starRepresentation (centralizer (V₁ : Set G)) V₃ V₁ hn hk) ≤ 2 := by
  let := d.elementary
  obtain ⟨c, hv, _⟩ := source_coordinates d
  have hC : centralizer ({c.singular.val} : Set G) = centralizer (V₁ : Set G) := by
    calc
      _ = centralizer (zpowers c.singular.val : Set G) := by
        rw [zpowers_eq_closure,centralizer_closure]
      _ = _ := congrArg (fun W : Subgroup G => centralizer (W : Set G)) c.line_eq
  let := SourceAbelian.source_closure_abelian_knownSimple d c.singular.val c.line_eq
    (by change ¬ centralizer ({c.singular.val} : Set G) ≤ _; rwa [hC]) hcounter
  have hT : (T : Subgroup G) ≤ centralizer ({c.singular.val} : Set G) := by
    rw [hC]
    exact d.flag.one_invariant.trans
      (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  have hcontains : residualCentralizer L (zpowers c.singular.val) ⊔ (T : Subgroup G) ≤
      centralizer ({c.singular.val} : Set G) := by
    rw [c.line_eq,hC]
    exact sup_le (map_subtype_le _ |>.trans inf_le_right) (hC ▸ hT)
  have h1357 : Earlier1357 T L V V₃ (zpowers c.singular.val)
      (centralizer ({c.singular.val} : Set G)) (normalizer (L : Set G)) := by
    rw [c.line_eq,hC]
    exact earlier1357_knownSimple d
  have hz2 : orderOf c.singular.val = 2 := by
    rw [←Nat.card_zpowers,c.line_eq]
    exact d.flag.one_card
  have hcv : centralizer ({c.nonsingular.val} : Set G) ≤ normalizer (V : Set G) := by
    simpa only [hv] using hCv
  have hfusion := d.flag.normalizer_controls_fusion_of_nonsingular_centralizer hCv
  have hex := exists_bounded_faithful_source_action c.coordinates c.nonsingular c.singular
    c.form_nonsingular c.singular_ne_one hz2 c.form_singular c.alternating_le hfusion hcv
    c.third_mark d.seed_normalizer_knownSimple hcontains (hC.symm ▸ houtside) h1357
    (earlierF923_of_source T L V V₃ (zpowers c.singular.val))
    (earlierF9163_of_five c.coordinates c.nonsingular c.singular c.form_nonsingular
      c.singular_ne_one c.form_singular c.alternating_le hfusion hcv c.third_mark
      d.seed_normalizer_knownSimple)
  let P (H W : Subgroup G) : Prop :=
    ∃ hU : IsElementaryAbelian 2 (Source.UH H V₃),
      letI := hU
      ∃ (hn : H ≤ normalizer (W : Set G))
        (hk : commutatorPreimage H (Source.UH H V₃) W = Source.QH H),
        Function.Injective (starRepresentation H V₃ W hn hk) ∧
        Representation.BinaryOffender.quadraticRatio (starRepresentation H V₃ W hn hk) ≤ 2
  change P _ _ at hex
  change P _ _
  exact (congrArg₂ P hC c.line_eq) ▸ hex

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
