module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Complete
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationSourceAt
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition.Complete
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FourRecognitionComplete

/-!+# The original 12.2.13 alternatives in the multiple-overgroup branch

If a centralizer of a nonidentity element of the original chosen V escapes
N_G(L), the first alternative holds. Otherwise the seven module rows give
global TI. The guarded H-star, cyclic and rigidity arguments construct the
split linear configuration, and its dimension-three or dimension-four
recognition gives precisely the marked PSL, A₉ or M₂₄ alternatives.

All fusion, local-configuration and terminal-recognition premises are
discharged here. Only the earlier structural and seven-module conclusions
of 12.2.2 at the same G,T remain explicit. Their source producers and final
discharge belong to qt-d-1222-source. The standing multiple-overgroup
hypothesis is retained; the universal unguarded APIs are unchanged.

Source: Aschbacher–Smith, 12.2.13–27, printed pp.799–807, with the standing
multiple-overgroup hypothesis following 2.1.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Both dimensions of 12.2.27, with actual ambient model isomorphisms. -/
theorem recognized_of_split_configuration
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {d : ℕ} (C : SplitLinearConfiguration L V d) (hnone : NoEscape L V) :
    RecognizedGroup G d := by
  rcases C.rank with hd | hd
  · subst d
    exact ThreeRecognition.recognizedGroup h D hnone C
  · subst d
    exact recognized_four h D C hnone

/-- Source 12.2.13 on every original choice of V, conditional only on the
earlier 12.2.2 inputs at the same G,T and the standing source guard. -/
theorem alternatives_of_modules_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Alternatives12213 T L V :=
  alternatives_of_ti_and_recognition_of_many_at h D structural modules hmany
    (fun hn => globalTI_of_module_alternatives_at h D structural hn (modules L V h D))
    (fun _ C hn => recognized_of_split_configuration h D C hn)

/-- The full ambient-local 12.2.13 contract: no fusion, local analysis or
recognition callback remains. The original L,V are universally quantified. -/
theorem theorem12213_of_modules_of_many_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Theorem12213At KnownSimple.IsKnownSimple T := by
  intro L V h D
  exact alternatives_of_modules_of_many_at h D structural modules hmany

/-- Apply the existing guarded seven-module producer without asking for
an unguarded module theorem or structure outside the original ambient G,T. -/
theorem theorem12213_of_modules_of_many
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Theorem12213At KnownSimple.IsKnownSimple T :=
  theorem12213_of_modules_of_many_at structural (modules.at T hmany) hmany

/-- Actual chosen-module source application: the same choice has both its
seven-row module classification and all four recognition alternatives. -/
theorem exists_chosen_source_results_of_many_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ∃ (V : Subgroup G) (D : ChosenModule T L V),
      ModuleAlternatives1222 D ∧ Alternatives12213 T L V :=
  exists_chosen_source_results_at structural modules
    (theorem12213_of_modules_of_many_at structural modules hmany) h

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
