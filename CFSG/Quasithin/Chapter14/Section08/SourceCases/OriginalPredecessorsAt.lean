module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.SourceAt
public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.OriginalAlternatingFiveFromRowsAt
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.FixedModuleRowsG2Source
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalSource.Applications
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.At.Naturality
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.CompleteAt

/-!
# Original D predecessors from the common Chapter12 sources

The faithful catalogue, original fixed and A5 module clauses, L3 naturality
and unitary exclusion use the same structural/module source inputs. The
larger-linear exclusion and actual H-star rank-one exits remain explicit.
No universal structural theorem or additional local recognition is inferred.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases.At
open Chapter12.Section02
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter13.Section01 Chapter13.Section01.SourceQuasisimple
open Chapter13.Section03.SourceClassification Chapter13.Section03.SourceCompletion
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

/-- Both original module clauses are consequences of the same earlier
Chapter12 sources, on the original full chosen modules. -/
theorem original_module_clauses_of_chapter12_at (h : Hypothesis1331 T L) :
    OriginalFixedModule1332At T L ∧ OriginalAlternatingFiveModules1332At T L := by
  have hq : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I) := by
    intro I hf
    exact h.hypothesis1311.faithful_quasisimple_of_source_inputs_at
      hmany structural modules larger
      ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T I).mpr ⟨hf.1.1,hf.2⟩)
  have hm : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I) := by
    intro I hi
    exact FiveQuotients.midSize
      (fiveQuotients_of_source_inputs_at h.hypothesis1311 hmany structural modules larger hi)
  exact ⟨originalFixedModule1332At_of_guarded_source h hmany hq hm structural modules exits,
    originalAlternatingFiveModules1332At_of_module_rows hq hm modules⟩

/-- Package the proved chosen-module naturality on every original L3 row.
The actual quotient projection, maximality and chosen module are retained. -/
theorem original_caseOne_of_chapter12_at : Earlier1332CaseOneAt T := by
  intro K d hq
  have hsource := (hypothesis1331 d).source1332OneTwo_of_source_inputs_at
    hmany structural modules larger
  refine ⟨faithfulMaximalLocal_of_source1332 d hsource,
    Section03.CaseOneSource.quotient_quasisimple hq, ?_⟩
  intro W D
  exact (chosen_natural_of_sources_at d hsource D hmany structural modules hq (exits K)).2

/-- The original unitary row has no independent exclusion input once the
common Chapter12 sources are supplied. -/
theorem original_unitary_exclusion_of_chapter12_at (h : Hypothesis1331 T L) :
    ¬ ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 3 := by
  obtain ⟨fixed,five⟩ := original_module_clauses_of_chapter12_at
    hmany structural modules larger exits h
  exact Chapter13.Section03.SourceCompletion.At.unitary_original_exclusion_of_module_sources
    h structural (RecognitionSource.theorem12213_of_modules_of_many_at
      structural modules hmany) modules
    (h.source1332OneTwo_of_source_inputs_at hmany structural modules larger) fixed five

/-- The later component sieve needs only the actual ordinary/covered six
recognition in addition to the common Chapter12 sources. -/
theorem original_faithful_classification_of_chapter12_at (d : Counterexample T L)
    (six : Theorem1381At T) :
    Chapter14.Section04.LargerDimension.LocalAction.Components.EarlierFaithfulClassification
      G (T : Subgroup G) := by
  exact earlierFaithfulClassification_of_sources_at d
    ((hypothesis1331 d).source1332OneTwo_of_source_inputs_at hmany structural modules larger)
    (fun K h => original_unitary_exclusion_of_chapter12_at
      hmany structural modules larger exits h) six

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At
