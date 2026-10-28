module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalPredecessorInterface
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.FromOriginalModuleSources

/-!
# Rudvalis from the common original Chapter12 sources

The fixed and A5 module clauses, unitary exclusion, faithful component sieve,
and 12.2.13 are now constructed from the shared earlier sources at the same
G,T. The original ordinary/covered six recognition and the existing universal
14.7.10 interface remain explicit. All later component and row arguments are
supplied internally on the unchanged original flag.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Chapter12.Section02 Chapter12.Section08
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original Rudvalis application with its fixed, five, unitary, faithful
and 12.2.13 inputs supplied from the common earlier Chapter12 sources. -/
theorem source_rudvalis_of_chapter12_sources_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
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
    (six : Theorem1381At T)
    (earlier : CriticalFusion.Source.ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    Nonempty (G ≃* Rudvalis.Model) := by
  obtain ⟨fixed,five⟩ := Section08.SourceCases.At.Interface.module_clauses
    hmany structural modules larger exits (hypothesis1331 d)
  exact source_rudvalis_of_original_module_sources_at d h hab structural
    (Section08.SourceCases.At.Interface.recognition hmany structural modules)
    (Section08.SourceCases.At.Interface.faithful_classification
      hmany structural modules larger exits d six) earlier fixed five

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
