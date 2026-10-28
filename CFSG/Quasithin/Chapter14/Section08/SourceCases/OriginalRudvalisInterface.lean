module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalPredecessorInterface
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl
import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.FromChapter12Sources

/-!
# The original abelian branch behind a narrow proof boundary

The full Rudvalis source is imported privately. Its original G,T,L,V,F
and the still-required universal 14.7.10 input remain unchanged.
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

/-- Recognize the original abelian flag from the common Chapter12 sources. -/
theorem rudvalis {V : Subgroup G} {F : InvariantFlag T V 3}
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (six : Theorem1381At T)
    (earlier : Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    Nonempty (G ≃* KnownSimple.SporadicName.ru.Carrier) :=
  Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource.source_rudvalis_of_chapter12_sources_at
    d h hab hmany structural modules larger exits six earlier

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
