module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalPredecessorInterface
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.LinearThreeAt
import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalPredecessorsAt

/-!
# Original quotient branches behind the narrow predecessor interface

The five-row catalogue, original L3 naturality and unitary exclusion are
proved from the same earlier Chapter12 sources. The large implementation
import is private to keep its proof dependency cone out of the final D
assembly; every mathematical object in these types is publicly imported.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
open Chapter12.Section02 Chapter12.Section08
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter13.Section03.SourceCompletion
open Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter14.Section03.FaithfulSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
  (larger : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
    ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (Chapter1.XiQuotient I) n 2)
  (exits : ∀ K H : Subgroup G,
    H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
    Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
    Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃*
      alternatingGroup (Fin 5)) →
    RankOneModule.GenericExit T (localResidual H) ∧
      RankOneModule.SmallExit T (localResidual H))

include hmany structural modules larger exits

/-- The original L3 chosen-module naturality implication at this same T. -/
theorem case_one : Earlier1332CaseOneAt T :=
  At.original_caseOne_of_chapter12_at hmany structural modules larger exits

omit exits in
/-- The actual five-row catalogue for the original counterexample. -/
theorem catalogue (d : Counterexample T L) : Source1332OneTwo T :=
  (hypothesis1331 d).source1332OneTwo_of_source_inputs_at hmany structural modules larger

/-- Exclude the unitary row on the same original counterexample. -/
theorem unitary (d : Counterexample T L) :
    ¬ ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 3 :=
  At.original_unitary_exclusion_of_chapter12_at
    hmany structural modules larger exits (hypothesis1331 d)

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
