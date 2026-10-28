module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalBranchInterface
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.LocalizedRudvalisInterface
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalNonabelianInterface

/-!
# The original D dispatcher with the Baumann source supplied internally

The abelian L3 branch now uses the original structural theorem at its own
group and Sylow. Every other branch retains its existing original source
inputs, including the marked HS endpoint and the full-catalogue A5 endpoint.
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

/-- The actual five-row source dispatcher without a universal 14.7.10 input. -/
theorem qtkeModel_of_local_original_sources
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
  have d := hmax.1
  have hL := (faithfulLocalComponents_iff L).mp d.local_component
  have hm : MidSizeModel (L ⧸ pCore 2 L) :=
    (Interface.catalogue hmany structural modules larger d L d.local_component).2
  rcases hm with h5 | h3 | h6 | hc6 | hu
  · exact five T L hmany hmax h5
  · obtain ⟨V, ⟨h⟩⟩ := SourceAssembly.At.exists_higherRankHypothesis d
      (Interface.case_one hmany structural modules larger exits) structural h3
    obtain ⟨_, F, _⟩ := h.exists_flag_geometry_at structural
    have hmodel : IsTheoremDModel G := by
      by_cases hU : IsMulCommutative F.U
      · exact .exceptional (.sporadic .ru (by simp)
          (Interface.rudvalis_local hmany structural modules larger exits d h hU six))
      · rcases Interface.nonabelian_original hmany structural modules larger exits d h F hU six with
          hG2 | ⟨z, hz, ht⟩
        · exact .exceptional (.g2_three hG2)
        · exact .exceptional (.sporadic .hs (by simp) (hs L V d h F hU z hz ht))
    exact hmodel.toQTKEModel
  · exact (not_A6_coreQuotient_of_source_at d six L hL.1 hL.2 h6).elim
  · exact (not_A6_cover_coreQuotient_of_source_at d six hL.1 hL.2 hc6).elim
  · exact (Interface.unitary hmany structural modules larger exits d hu).elim

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At
