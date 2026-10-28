module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearResidualFSUApplication

/-!
# Maximality and nonfaithfulness of the original exceptional residual

Both earlier source exclusions are now proved: a proper containing component
cannot retain the literal diagram actor, and an actual faithful Fundamental
Setup cannot support it. Apply them to the original H-star residual and then
feed the existing source geometry. Every quotient and normalization is the
one in the chosen Chapter12 setup; no embedding, FSU or model callback remains.
The further field-exponent and whole-module conclusions of5.1.14 remain with
qt-d-1222-rankone-exceptional-linear-analysis.

Source: Aschbacher–Smith5.1.14(1–2), printed pp.638–639, applied in12.2.2,
printed pp.794–795 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- Both residual assertions, with both earlier source exclusions discharged. -/
theorem linear_residual_maximal_nonfaithful
    {T : Sylow 2 G} {M H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∧
      ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) :=
  linear_residual_maximal_nonfaithful_of_embedding_exclusion hG hmany hTM hH hlinear
    (linearFourEmbeddingExclusion hG)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal Chapter12 instance of the maximal and nonfaithful residual. -/
theorem rankOne_linear_residual_maximal_nonfaithful
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∧
      ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) :=
  linear_residual_maximal_nonfaithful h.simpleQTKE hmany
    D.sylow_normalizes_component hH hlinear

/-- The existing geometry applied unconditionally to the same original residual. -/
theorem rankOne_linear_residual_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    residual H ≤ omegaCentralizer T ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
        N = normalizer (residual H : Set G) := by
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact residual_geometry_of_maximal_nonfaithful h.simpleQTKE hH.1.1 hm hf
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
