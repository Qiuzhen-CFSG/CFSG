module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalPredecessorInterface
import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.FromLocalModuleSources

/-!
# Rudvalis using the original structural source at the same Sylow

The natural-point Baumann theorem supplies the earlier 14.7.10 alternative
where the original proof uses it. The remaining fixed and A5 module clauses,
faithful classification and 12.2.13 come from the common Chapter12 sources.
The proof implementation is private so consumers retain a narrow boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
open Chapter12.Section02 Chapter12.Section08
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter13.Section03.SourceCompletion
open Chapter14.Section03.FaithfulSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Recognize the original abelian flag using only source inputs at its
actual group and Sylow; the earlier Baumann alternative is proved internally. -/
theorem rudvalis_local
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
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) (six : Theorem1381At T) :
    Nonempty (G ≃* KnownSimple.SporadicName.ru.Carrier) := by
  obtain ⟨fixed, five⟩ := module_clauses
    hmany structural modules larger exits (hypothesis1331 d)
  exact Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource.source_rudvalis_of_local_module_sources_at
    d h hab structural (recognition hmany structural modules)
    (faithful_classification hmany structural modules larger exits d six) fixed five

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
