module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualFSURecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearResidual

/-!
# The recognized irreducible FSU obstruction on the Chapter 12 residual

Apply the literal chosen-module normalization and H* hypotheses to exclude
irreducibility of any FSU component action on the original residual module.
The conditional applications then feed nonfaithfulness into the unchanged
centralization and exact maximal-overgroup uniqueness theorem.

Maximality and source irreducibility remain with
qt-d-1222-linear-residual-maximal-nonfaithful; these are not assumptions
discharged by the present applications. The final source theorem belongs to
qt-d-1222-rankone-exceptional-linear-analysis.
Source: Aschbacher–Smith 5.1.14, printed pp.638–639, as used in 12.2.2
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 residual excludes the irreducible FSU branch. -/
theorem rankOne_linear_residual_fsu_not_irreducible
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T (residual H)) :
    letI := F.module_elementary
    ¬ Representation.IsIrreducible (F.joinRepresentation.comp F.componentActionImage.subtype) :=
  linear_residual_fsu_not_irreducible D.sylow_normalizes_component hmany hH hlinear F

/-- Conditional assembly with irreducibility, without a model-marking premise. -/
theorem rankOne_linear_residual_nonfaithful_of_fsu_irreducible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hi : ∀ F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T
      (residual H), letI := F.module_elementary
        Representation.IsIrreducible (F.joinRepresentation.comp F.componentActionImage.subtype)) :
    ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) :=
  linear_residual_nonfaithful_of_fsu_irreducible h.simpleQTKE
    D.sylow_normalizes_component hmany hH hlinear hmax hi

/-- Feed the actual nonfaithfulness conclusion into the existing geometry. -/
theorem rankOne_linear_residual_geometry_of_fsu_irreducible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hi : ∀ F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T
      (residual H), letI := F.module_elementary
        Representation.IsIrreducible (F.joinRepresentation.comp F.componentActionImage.subtype)) :
    residual H ≤ omegaCentralizer T ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
        N = normalizer (residual H : Set G) :=
  residual_geometry_of_maximal_nonfaithful h.simpleQTKE hH.1.1 hmax
    (D.rankOne_linear_residual_nonfaithful_of_fsu_irreducible h hmany hH hlinear hmax hi)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
