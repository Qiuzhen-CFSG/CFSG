module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalBranchInterface
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Type
import CFSG.Quasithin.Chapter14.Section08.SourceCases.NonabelianOnlyHS

/-!
# The original nonabelian flag after G2 recognition

The proved original G2 configuration recognition is consumed internally.
The remaining HS alternative retains the original seed and flag point.
The large independent recognition proof is a private implementation import.
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

/-- Only the actual original HS local type remains after the G2 branch. -/
theorem nonabelian_original {V : Subgroup G}
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (six : Theorem1381At T) :
    ClassificationModels.IsG2At G 3 ∨
      ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  nonabelian_recognition_or_original_hs_at d h
    (case_one hmany structural modules larger exits) structural
    (recognition hmany structural modules)
    (faithful_classification hmany structural modules larger exits d six) F hne

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
