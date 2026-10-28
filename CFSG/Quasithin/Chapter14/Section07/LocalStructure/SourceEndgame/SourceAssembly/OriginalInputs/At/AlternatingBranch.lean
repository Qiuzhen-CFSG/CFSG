module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.OriginalBranch
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition

/-!
# The local alternating recognition feeds the original Rudvalis branch

The actual alternating residual now supplies natural recognition on the
original section, with its full S₅ action and exact K-fixed kernel. Apply
this proof to the existing original-branch consumer to construct Data and
obtain both the concrete Rudvalis isomorphism and the full D-model conclusion.

For general residual alternatives, uniqueness is retained because the G₂
exclusion uses it. On the alternating branch, the index-five argument proves
uniqueness internally. Neither application assumes a recognition callback.
The original counterexample, local structural, faithful-family and A₅-module
inputs retain their earlier-source producers. Final unconditional assembly
remains with the source-data, 14.7.75 and Theorem-D owners.

Source: Aschbacher–Smith 14.7.40, 14.7.52–75, printed pp.1063–1078, and J.1.1.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Chapter12.Section08 CriticalFusion.Source CriticalFusion.SourceConstruction
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section03.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
  (d : Counterexample T L)
  (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
  (hab : IsMulCommutative F.U)
  (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (five : OriginalAlternatingFiveModules1332At T L)
include d h hab structural faithful five

/-- The residual-alternatives application with natural recognition proved
at the original G,T. Uniqueness remains an input to the G₂ exclusion. -/
theorem source_rudvalis_of_original_residual_alternatives_at
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (h52 : AlternatingResidual F ∨ G2Residual F) : Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_original_branches_at d h hab hunique structural faithful five h52
    (LocalReduction.naturalRecognition_of_alternating_at h hab structural)

/-- The same original residual alternatives yield the full D-model conclusion. -/
theorem source_theoremDModel_of_original_residual_alternatives_at
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (h52 : AlternatingResidual F ∨ G2Residual F) : ClassificationModels.IsTheoremDModel G :=
  source_theoremDModel_of_original_branches_at d h hab hunique structural faithful five h52
    (LocalReduction.naturalRecognition_of_alternating_at h hab structural)

/-- On the alternating branch both uniqueness and natural recognition are
proved internally, before applying the original Rudvalis consumer. -/
theorem source_rudvalis_of_original_alternating_at
    (hAlt : AlternatingResidual F) : Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_original_residual_alternatives_at d h hab structural faithful five
    (LocalReduction.unique_of_alternating_at h hab structural hAlt) (Or.inl hAlt)

/-- The alternating branch supplies the full D model with no uniqueness
or recognition callback among its premises. -/
theorem source_theoremDModel_of_original_alternating_at
    (hAlt : AlternatingResidual F) : ClassificationModels.IsTheoremDModel G :=
  source_theoremDModel_of_original_residual_alternatives_at d h hab structural faithful five
    (LocalReduction.unique_of_alternating_at h hab structural hAlt) (Or.inl hAlt)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
