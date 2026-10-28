module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.MaximalCounterexample
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.SourceElimination
/-!
# The seed closure at the actual maximal Theorem D counterexample

The original maximal counterexample supplies Hypothesis12.2.1 for its
ordinary A₆ local component. Apply the completed13.5 seed-closure theorem
to the unchanged natural flag. The order-two line identifies its point
normalizer with its centralizer, preserving the literal G₁ used by13.7.
No F.9 application or escaping local subgroup is assumed.
Source: Aschbacher–Smith13.5.12 and13.7.2, printed pp.918,935–936.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section05.ComponentReduction.OriginalSix
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
/-- The actual maximal ordinary-A₆ counterexample has abelian point-normalizer seed closure. -/
theorem original_six_seed_span_abelian
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L)≃*alternatingGroup (Fin 6)) :
    IsMulCommutative (conjugateSpanBy V₃ G₁) := by
  let D := Chapter13.Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁
  have heq : G₁=D.Gz := d.first_normalizer.trans
    (le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.line_card)
      (Subgroup.centralizer_le_normalizer _))
  have d' : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz := heq ▸ d
  have hh := source_point_seed_abelian d' e
    (hypothesis1221_of_maximal_natural_six d' hmax e)
  change IsMulCommutative (conjugateSpanBy V₃ D.Gz) at hh
  exact heq.symm ▸ hh
end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
