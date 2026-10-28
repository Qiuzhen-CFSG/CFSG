module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FourRecognitionIsolation
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionNormality

/-!
# The dimension-four recognition in 12.2.27(1)

The original affine translations identify a distinguished root group.
Their normalizer moves the marked point and excludes Held's local type.
The isolated-root normality theorem completes the source fusion alternatives,
and the actual linear and Mathieu uniqueness isomorphisms give the two
recognition conclusions. The original configuration's block then supplies
the corresponding Alternatives12213 branch.

All earlier-source inputs are precisely the original chosen module,
no-escape hypothesis and independent split linear configuration. Source:
Aschbacher–Smith, 12.2.27(1), p.807; Aschbacher, *Sporadic Groups* (1994),
39.9–41.6, pp.216–222. The section assembly owns construction of the split
configuration and umbrella integration.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 12.2.27(1), retaining the original split linear configuration. -/
theorem four_recognition {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) :=
  four_recognition_of_isolation_normality h D C hnone
    (fun _ F => TransvectionFive.CoreFusion.row_isolation_normal F)

/-- The dimension-four recognition interface has no remaining local callbacks. -/
theorem recognized_four {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V) :
    RecognizedGroup G 4 :=
  recognized_four_of_classical_or_mathieu (four_recognition h D C hnone)

/-- The original configuration's literal block supplies the dimension-four
branch of 12.2.13. -/
theorem alternatives_four {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V) :
    Alternatives12213 T L V :=
  alternatives_four_of_classical_or_mathieu C (four_recognition h D C hnone)

/-- Both original consumers, with all local marking, fusion and uniqueness
premises discharged. -/
theorem four_consumers {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V) :
    RecognizedGroup G 4 ∧ Alternatives12213 T L V :=
  ⟨recognized_four h D C hnone,alternatives_four h D C hnone⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
