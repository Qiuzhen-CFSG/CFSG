module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalG2
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.LocalAlternatives.SevenSource

/-!
# Rudvalis assembly from the original residual branches

The original G₂ exclusion now constructs its core commutator and both
orbit inputs. The surviving alternating recognition constructs Data, and
the proved fixed-component alternatives and natural-point Baumann input
finish the literal Rudvalis and full Theorem-D model consumers.

No Data, G₂ exclusion, core identity, orbit implication, fixed-component
alternative or MS classifier is assumed. The earlier structural, faithful
and alternating-module source theorems, together with the uniqueness,
component and alternating recognition conclusions of14.7.52/63, remain
explicit. Their source construction and the specialization to the original
G,T must still be discharged by the existing assembly owners. In particular,
a Structural1222At premise does not imply the universal Structural1222 API
preserved here. These are conditional source consumers, not unconditional
14.7.75 or Theorem D.

Source: Aschbacher–Smith14.7.52–75, pp.1065–1078.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Chapter12.Section08 CriticalFusion.Source CriticalFusion.SourceConstruction
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
  (d : Counterexample T L)
  (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
  (hab : IsMulCommutative F.U)
  (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
  (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
  (h52 : AlternatingResidual F ∨ G2Residual F)
  (h40 : AlternatingResidual F → NaturalRecognition F)
include d h hab hunique hcomponent structural faithful modules h52 h40

/-- The actual Rudvalis isomorphism from the earlier original source branches. -/
theorem source_rudvalis_of_original_branches : Nonempty (G ≃* Rudvalis.Model) := by
  obtain ⟨W,add,mod,⟨datum⟩⟩ := OriginalG2.exists_data_of_original_g2_exclusion
    d h hab hunique hcomponent structural faithful h52 h40
  exact source_rudvalis_of_original_fixed_components datum structural faithful modules

/-- The same original branch supplies the complete D-model conclusion. -/
theorem source_theoremDModel_of_original_branches : ClassificationModels.IsTheoremDModel G := by
  obtain ⟨W,add,mod,⟨datum⟩⟩ := OriginalG2.exists_data_of_original_g2_exclusion
    d h hab hunique hcomponent structural faithful h52 h40
  exact source_theoremDModel_of_original_fixed_components datum structural faithful modules

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
