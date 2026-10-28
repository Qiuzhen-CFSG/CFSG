module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.OriginalG2
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Assembly

/-!
# The original residual branches feed the local Rudvalis assembly

Exclude the genuine G₂ residual on the original flag, constructing its
core commutator, faithful section action, selected path and orbit inputs.
The actual residual alternatives supply the relative C-component.
The surviving alternating recognition constructs Data on the same G,T,L,V,F.
Apply the completed local endgame to obtain the concrete Rudvalis isomorphism
and the full Theorem-D model conclusion.

Only the original local structural, faithful-family and A₅-module inputs
remain alongside the residual alternatives, uniqueness and alternating
recognition owned by qt-d-14763-source-data. Their actual
source proofs remain necessary: these conditional applications do not finish
original 14.7.75. Final discharge remains with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.52–75, pp.1065–1078, and J.1.1.
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
  (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
  (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (five : OriginalAlternatingFiveModules1332At T L)
  (h52 : AlternatingResidual F ∨ G2Residual F)
  (h40 : AlternatingResidual F → NaturalRecognition F)
include d h hab hunique structural faithful five h52 h40

/-- The actual Rudvalis isomorphism, with Data constructed from the earlier
original branches and all structural uses confined to the same G,T. -/
theorem source_rudvalis_of_original_branches_at : Nonempty (G ≃* Rudvalis.Model) := by
  obtain ⟨W,add,mod,⟨datum⟩⟩ := OriginalG2.exists_data_of_original_g2_exclusion_at
    d h hab hunique (LocalReduction.component_of_residual_alternatives h52)
      structural faithful h52 h40
  exact source_rudvalis_from_original_modules_at datum structural faithful five

/-- The same original branch supplies the full D-model conclusion. -/
theorem source_theoremDModel_of_original_branches_at : ClassificationModels.IsTheoremDModel G := by
  obtain ⟨W,add,mod,⟨datum⟩⟩ := OriginalG2.exists_data_of_original_g2_exclusion_at
    d h hab hunique (LocalReduction.component_of_residual_alternatives h52)
      structural faithful h52 h40
  exact source_theoremDModel_from_original_modules_at datum structural faithful five

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
