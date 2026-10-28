module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualReduction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinear

/-!
# The exceptional residual diagram in the original Chapter 12 setup

The chosen-module normalization and actual H* membership supply the nontrivial
diagram actor on the embedded residual, with no further source premise.
The two remaining exclusions are then applied to this same residual to obtain
maximality and nonfaithfulness, and the existing geometric theorem gives
centralization and the exact maximal-overgroup normalizer.

Only the graph-action theorem is unconditional. The two source exclusions
remain explicit in the assembly exports; neither is discharged by this module.
The original exponent and generation-parameter assumptions are unnecessary
for these steps once the residual quotient is PSL₃(4).
Source: Aschbacher–Smith, opening of 5.1.14, printed pp.638–639, as used by
12.2.2 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The genuine 5.1.10 diagram clause on the literal Chapter 12 residual. -/
theorem rankOne_linear_residual_graph_action
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    HasLinearFourGraphAction (T : Subgroup G) (residual H) :=
  linear_residual_graph_action T D.sylow_normalizes_component hH hlinear

/-- The requested residual assertions, conditional on their two earlier source exclusions. -/
theorem rankOne_linear_residual_maximal_nonfaithful_of_exclusions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hemb : LinearFourEmbeddingExclusion G) (hfsu : LinearFourFSUDiagramExclusion G) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∧
      ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) :=
  linear_residual_maximal_nonfaithful_of_exclusions h.simpleQTKE hmany
    D.sylow_normalizes_component hH hlinear hemb hfsu

/-- The existing source geometry consumes the two residual assertions on the
same subgroup and gives the normalizer required by the exceptional assembly. -/
theorem rankOne_linear_residual_geometry_of_exclusions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hemb : LinearFourEmbeddingExclusion G) (hfsu : LinearFourFSUDiagramExclusion G) :
    residual H ≤ omegaCentralizer T ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
        N = normalizer (residual H : Set G) := by
  obtain ⟨hm, hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful_of_exclusions
    h hmany hH hlinear hemb hfsu
  exact residual_geometry_of_maximal_nonfaithful h.simpleQTKE hH.1.1 hm hf

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
