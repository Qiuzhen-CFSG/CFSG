module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.MaximalCounterexample
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.SourceHypothesis

/-!
# The selected ordinary A₆ source configuration for Theorem D

A maximal original counterexample supplies Hypothesis12.2.1 for its natural
A₆ component. The literal escaping subgroup and its nonabelian seed closure
then supply the full F.9 application and all four pre-B.4 source conditions
for one selected component. The maximality is the choice made at the original
Theorem D entry, rather than an additional local classification premise.
Source: Aschbacher–Smith13.5.7 and13.5.18–21, pp.918,922–923.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section05.ComponentReduction.Recognition
open Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Chapter13.Section05.ComponentReduction.OriginalSix
universe u
variable {G : Type u} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G}

/-- The original maximal choice discharges the final earlier-local premise
of the selected ordinary A₆ configuration. -/
theorem original_six_source_configuration
    (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
    (hmax : Maximal (Counterexample D.T) D.L)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hH : D.H ∈ Chapter13.Section08.Source.Hz D.L₁ D.T D.Gz M)
    (hU : ¬IsMulCommutative D.UH) :
    ∃ h : D.Hypothesis, ∃ K : Subgroup G, ∃ s : Selected D K,
      let := componentCentralizer_normal s h
        (selected_star_local_normalization s h d.counterexample.qtke (selected_H_mem h))
      SourceConfiguration s h D.L₁ le_rfl :=
  source_exists_configuration d e
    (hypothesis1221_of_maximal_natural_six d hmax e) hH hU
end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
