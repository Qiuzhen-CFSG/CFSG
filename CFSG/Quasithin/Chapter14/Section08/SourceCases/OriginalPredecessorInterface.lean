module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.At.Classification
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterRankOneSources
import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalPredecessorsAt

/-!
# Public interface for the original Chapter12 predecessor consequences

The proof implementation is imported privately so clients of these
results do not re-export its complete source-proof dependency cone. The
public imports expose every mathematical object appearing in the types.
This boundary avoids the host memory-mapping limit when combining the
predecessors with the independent Rudvalis endgame.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
open Chapter12.Section02
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter13.Section03.SourceCompletion
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

omit larger exits in
/-- The original 12.2.13 recognition consequence at the same Sylow subgroup. -/
theorem recognition : Theorem12213At KnownSimple.IsKnownSimple T :=
  RecognitionSource.theorem12213_of_modules_of_many_at structural modules hmany

/-- The original fixed and A5 module clauses at the original G,T. -/
theorem module_clauses (h : Hypothesis1331 T L) :
    OriginalFixedModule1332At T L ∧ OriginalAlternatingFiveModules1332At T L :=
  CFSG.Quasithin.Chapter14.Section08.SourceCases.At.original_module_clauses_of_chapter12_at hmany structural modules larger exits h

/-- The faithful component sieve, retaining actual ordinary/covered six recognition. -/
theorem faithful_classification (d : Counterexample T L)
    (six : Theorem1381At T) :
    Chapter14.Section04.LargerDimension.LocalAction.Components.EarlierFaithfulClassification
      G (T : Subgroup G) :=
  CFSG.Quasithin.Chapter14.Section08.SourceCases.At.original_faithful_classification_of_chapter12_at
    hmany structural modules larger exits d six

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
