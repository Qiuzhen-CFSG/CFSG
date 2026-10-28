module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases.LocalizedOriginalSourcesAt
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.InitialNaturalInterface

/-!
# Original D sources with the larger-linear terminal supplied internally

The known D-model branch is dispatched first. In the remaining branch the
actual maximal counterexample supplies Hypothesis1311, so Section09's
larger-linear exclusion is used under its genuine ambient exclusions.
Only the initial degree-four natural marking remains as a source duty.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases.At
open ClassificationModels Chapter1.Section02.LocalModels
open Chapter12.Section02 Chapter12.Section08
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual D branch from same-ambient source inputs and the remaining
initial degree-four marking, preserving all other original duties. -/
theorem qtkeModel_of_initial_natural_sources
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (four : ∀ L V : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2 →
      Chapter12.Section09.NaturalModule D 4)
    (exits : ∀ K H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃*
        alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H))
    (six : Theorem1381At T)
    (hs : ∀ (L V : Subgroup G) (_d : Counterexample T L)
      (_h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
      (F : InvariantFlag T V 3), ¬ IsMulCommutative F.U →
      ∀ z : G, F.Vi 1 = zpowers z → HigmanSims.TypeAt z V →
        Nonempty (G ≃* KnownSimple.SporadicName.hs.Carrier))
    (five : FiveRecognition G)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) : IsQTKEModel G := by
  classical
  by_cases hD : IsTheoremDModel G
  · exact hD.toQTKEModel
  obtain ⟨L, hmax⟩ :=
    LieTypeBranch.exists_maximal_counterexample_of_not_theoremDModel hG T hne hD
  have larger := Interface.larger_linear_of_initial_natural
    (hypothesis1331 hmax.1).hypothesis1311 structural modules hmany four
  exact qtkeModel_of_local_original_sources hmany structural modules larger
    exits six hs five hG hne

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At
