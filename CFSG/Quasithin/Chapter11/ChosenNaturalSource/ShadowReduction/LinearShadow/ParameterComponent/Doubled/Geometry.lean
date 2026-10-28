module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Generation
public import CFSG.Quasithin.ChapterE.Section03.Parameters.RankKernel

/-!
# The remaining doubled local geometry

These are the outputs of the first five paragraphs of source 11.3.6.
They concern the full original V_M and its literal automizer. They are
proof targets, not additional standing hypotheses or asserted source results.
The parameter collapse below consumes the first two outputs; the rank-one
module comparison consumes the strict r-bound and automizer rank budget.

Source: Aschbacher--Smith, 11.3.6, printed p.772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The source M/C_M(V_M), before any replacement by a matrix group. -/
abbrev LocalQuotient (L V : Subgroup G) :=
  (normalizer (L : Set G)) ⧸
    centralizer ((fullModule L V).subgroupOf (normalizer (L : Set G)) :
      Set (normalizer (L : Set G)))

/-- Outputs to be proved from the doubled source configuration. -/
structure Geometry (d : Coordinates D S) (H : Subgroup G) : Prop where
  weak_escape : ¬ ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤
    H.pCoreIn 2
  s_value : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) =
    (2 * S.field.degree : ℕ∞)
  r_bound : (2 * S.field.degree : ℕ∞) < ChapterE.globalR (fullModule L V)
  automizer_rank : primeRank 2
    (ChapterE.inducedAutomizer (fullModule L V) (normalizer (L : Set G))) ≤
      3 * S.field.degree

variable {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}

/-- Application of the local geometry to the source parameter and component.
The source geometry producer must still construct Geometry. -/
theorem parameter_and_component (h : Hypothesis1131At D S U₁ H)
    (d : Coordinates D S) (z : Geometry d H) (r : RankOneReduction S H)
    (hu : ChapterE.generationParameter H ≤ 2 * S.field.degree) :
    ChapterE.generationParameter H = 2 * S.field.degree ∧
      Source.NormalComponentIn H (residual H) ∧
      ClassicalGroup.IsPSL ((residual H) ⧸ pCore 2 (residual H))
        2 (2 ^ (2 * S.field.degree)) :=
  ⟨parameter_eq_twice h d z.weak_escape z.s_value hu,
    residual_component h d r z.weak_escape z.s_value hu⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
