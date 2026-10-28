module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalBranchInterface
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalRudvalisInterface
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalNonabelianInterface

/-!
# The original five-row D dispatcher from common source inputs

The Chapter12 sources construct the catalogue, original chosen-module
naturality, unitary exclusion and faithful component sieve. The original
13.8.1 implication eliminates both six-letter rows. On the actual L3 flag,
the abelian branch is the proved Rudvalis source; the nonabelian G2 branch
is recognized internally. Only recognition of the literal original HS type
and the genuine A5 endpoint remain, alongside the earlier source inputs.

The HS premise keeps the same counterexample, higher-rank hypothesis, flag,
point and seed. It does not assert recognition for arbitrary HS local types.
The full-model A5 conclusion is never narrowed to the strict D catalogue.
Source: Aschbacher--Smith 14.8.1--2, printed pp.1078--1079.
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

  (six : Theorem1381At T)
  (earlier : Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.Earlier14710.{u})
  (hs : ∀ (L V : Subgroup G) (_d : Counterexample T L)
    (_h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3), ¬ IsMulCommutative F.U →
    ∀ z : G, F.Vi 1 = zpowers z → HigmanSims.TypeAt z V →
      Nonempty (G ≃* KnownSimple.SporadicName.hs.Carrier))

include hmany structural modules larger exits six earlier hs

/-- The original L3 row, with both source branches constructed internally
and only its actual marked HS recognition endpoint retained. -/
theorem theoremDModel_of_original_linearThree {L : Subgroup G}
    (d : Counterexample T L) (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) :
    IsTheoremDModel G := by
  classical
  obtain ⟨V,⟨h⟩⟩ := SourceAssembly.At.exists_higherRankHypothesis d
    (Interface.case_one hmany structural modules larger exits) structural hq
  obtain ⟨_,F,_⟩ := h.exists_flag_geometry_at structural
  by_cases hU : IsMulCommutative F.U
  · exact .exceptional (.sporadic .ru (by simp)
      (Interface.rudvalis hmany structural modules larger exits d h hU six earlier))
  · rcases Interface.nonabelian_original hmany structural modules larger exits d h F hU six with
      hG2 | ⟨z,hz,ht⟩
    · exact .exceptional (.g2_three hG2)
    · exact .exceptional (.sporadic .hs (by simp) (hs L V d h F hU z hz ht))

/-- Exhaust the five actual quotient rows. Both A6 rows use the same
Theorem1381At input already required by the faithful source sieve. -/
theorem theoremDModel_or_five_of_original_sources
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) :
    IsTheoremDModel G ∨ ∃ L : Subgroup G,
      Maximal (Counterexample T) L ∧ IsAlternating (L ⧸ pCore 2 L) 5 := by
  classical
  by_cases hD : IsTheoremDModel G
  · exact Or.inl hD
  obtain ⟨L,hmax⟩ :=
    LieTypeBranch.exists_maximal_counterexample_of_not_theoremDModel hG T hne hD
  have d := hmax.1
  have hL := (faithfulLocalComponents_iff L).mp d.local_component
  have hm : MidSizeModel (L ⧸ pCore 2 L) :=
    (Interface.catalogue hmany structural modules larger d L d.local_component).2
  rcases hm with h5 | h3 | h6 | hc6 | hu
  · exact Or.inr ⟨L,hmax,h5⟩
  · exact Or.inl (theoremDModel_of_original_linearThree
      hmany structural modules larger exits six earlier hs d h3)
  · exact (not_A6_coreQuotient_of_source_at d six L hL.1 hL.2 h6).elim
  · exact (not_A6_cover_coreQuotient_of_source_at d six hL.1 hL.2 hc6).elim
  · exact (Interface.unitary hmany structural modules larger exits d hu).elim

/-- The strict D catalogue from the exact original A5 pair of models. -/
theorem theoremDModel_of_original_sources
    (five : ∀ L : Subgroup G, Maximal (Counterexample T) L →
      IsAlternating (L ⧸ pCore 2 L) 5 →
        ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) : IsTheoremDModel G := by
  rcases theoremDModel_or_five_of_original_sources
    hmany structural modules larger exits six earlier hs hG hne with hD | ⟨L,hmax,h5⟩
  · exact hD
  · rcases five L hmax h5 with hu | hl
    · exact .exceptional (.unitary_binary hu)
    · exact .exceptional (.linear_three hl)

/-- The full Main-Theorem output using the genuine A5 terminal endpoint.
No full-model conclusion is narrowed to the strict D catalogue. -/
theorem qtkeModel_of_original_sources
    (five : FiveRecognition G)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) : IsQTKEModel G := by
  rcases theoremDModel_or_five_of_original_sources
    hmany structural modules larger exits six earlier hs hG hne with hD | ⟨L,hmax,h5⟩
  · exact hD.toQTKEModel
  · exact five T L hmany hmax h5

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At
