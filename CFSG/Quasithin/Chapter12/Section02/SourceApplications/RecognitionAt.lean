module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.CompleteAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At

/-!
# The completed guarded recognition at the original Chapter13 consumer

The ambient exclusions of 13.1.1 eliminate every global model alternative
of 12.2.13. Thus every original chosen module has a nonidentity element
whose centralizer escapes its original N_G(L). The structural theorem also
selects such a module, preserving its T-invariance and seven-module row.

The recognition premise in the existing Chapter13 application is discharged.
Only the earlier 12.2.2 structural and module inputs and the standing
multiple-overgroup guard remain. Their final source discharge belongs to
qt-d-1222-source; these are the same inputs used by qt-d-1332-source.
Source: Aschbacher–Smith, 12.2.13, 13.1.2 and 13.3.2.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
open Chapter13.Section01 RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Source 13.1.2 escape on the original chosen V, with 12.2.13 supplied. -/
theorem centralizer_escape_of_many_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h : Hypothesis1311 T) {L V : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (D : ChosenModule T L V) :
    ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) :=
  centralizer_escape (theorem12213_of_modules_of_many_at structural modules hmany)
    h hL hq D

/-- The actual classified, invariant, escaping choice used in Chapter13,
with no remaining recognition assumption. -/
theorem exists_classified_chosen_escape_of_many_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    ∃ (V : Subgroup G) (D : ChosenModule T L V),
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      ModuleAlternatives1222 D ∧
      ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) :=
  exists_classified_chosen_escape structural modules
    (theorem12213_of_modules_of_many_at structural modules hmany) h hL hq

end CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
