module
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import CFSG.Quasithin.Chapter6.SourceDefs
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# Original earlier module clauses for the unitary source argument

These are the two universal specializations of 13.3.2(3) used by the
unitary proof: a chosen module with nonzero fixed space is the augmentation
core for A₆, and a chosen module of an A₅ component is its alternating
natural module. Both retain the original Hypothesis 13.3.1 and the literal
chosen-module action. The five-dimensional row uses the faithful quotient
by the module centralizer, which need not equal the two-core.

These definitions state earlier-source premises, not proved theorems.
Their existing producer is qt-d-1332-source. Final discharge belongs to
qt-d-13316-source. No later Chapter 13.7 exclusions are assumed.
Source: Aschbacher--Smith 13.3.2(3), printed p.885.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02 Chapter14.Section03.FaithfulSource ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- The fixed-space clause of original 13.3.2(3), without the later 13.7 exclusions.
The source producer is qt-d-1332-source; final discharge is retained by
qt-d-13316-source. This is an earlier-source premise, not an asserted theorem. -/
@[expose] def OriginalFixedModule1332At (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  Hypothesis1331 T L → ∀ K ∈ MainForward.faithfulLocalComponents T,
    ∀ W : Subgroup G, ∀ C : ChosenModule T K W,
      letI := C.actionCentralizer_normal
      W ⊓ centralizer (K : Set G) ≠ ⊥ →
      Nonempty (ActionEquiv C.faithfulAction
        (BinaryPermutation.alternatingCoreRepresentation (Fin 6)))

/-- The A₅ specialization of original 13.3.2(3), on each actual chosen module.
Its source producer is qt-d-1332-source; qt-d-13316-source retains the final
discharge. No later Chapter 13.7 exclusion is imposed. -/
@[expose] def OriginalAlternatingFiveModules1332At (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  Hypothesis1331 T L → ∀ K ∈ MainForward.faithfulLocalComponents T,
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
    ∀ I : Subgroup G, ChosenModule T K I →
      Chapter6.Source.IsConjugationModel K I Chapter6.Source.a5Module

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
