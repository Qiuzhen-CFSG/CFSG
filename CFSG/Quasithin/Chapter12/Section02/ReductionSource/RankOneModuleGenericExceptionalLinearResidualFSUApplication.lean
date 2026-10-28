module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearResidualFSUComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearResidual

/-!
# Original Chapter12 applications of the completed FSU exclusion

Apply the exact shared FSU exclusion to the embedded two-residual of the
original H-star member. No tensor marking, irreducibility or seed-orbit
premise remains. Maximality alone now gives nonfaithfulness, and the unchanged
source geometry gives centralization and exact maximal-overgroup uniqueness.

The proper containing-component exclusion, with its remaining J₄ case, is
still owned by qt-d-1222-linear-residual-maximal-nonfaithful. These conditional
applications do not establish unconditional5.1.14(1); final assembly remains
with qt-d-1222-rankone-exceptional-linear-analysis.
Source: Aschbacher–Smith5.1.14, printed pp.638–639, applied in12.2.2,
pp.794–795 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- On the literal Chapter12 residual, maximality implies nonfaithfulness. -/
theorem rankOne_linear_residual_nonfaithful_of_maximal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) :=
  linear_residual_nonfaithful_of_maximal h.simpleQTKE hmany
    D.sylow_normalizes_component hH hlinear hmax

/-- Only the containing-component exclusion remains in the shared assembly. -/
theorem rankOne_linear_residual_maximal_nonfaithful_of_embedding_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hemb : LinearFourEmbeddingExclusion G) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∧
      ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) :=
  linear_residual_maximal_nonfaithful_of_embedding_exclusion h.simpleQTKE hmany
    D.sylow_normalizes_component hH hlinear hemb

/-- The original residual geometry now requires only maximality. -/
theorem rankOne_linear_residual_geometry_of_maximal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    residual H ≤ omegaCentralizer T ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
        N = normalizer (residual H : Set G) :=
  residual_geometry_of_maximal_nonfaithful h.simpleQTKE hH.1.1 hmax
    (D.rankOne_linear_residual_nonfaithful_of_maximal h hmany hH hlinear hmax)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
