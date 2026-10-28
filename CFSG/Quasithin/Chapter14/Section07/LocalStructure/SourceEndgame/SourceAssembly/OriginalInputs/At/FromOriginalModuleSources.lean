module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentSourceAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Assembly

/-!
# Rudvalis from the original earlier module sources

The earlier fixed-module theorem now supplies the actual component assertion
14.7.47 as well as the local row exclusions. Construct Data on the original
flag and apply the marked Rudvalis endgame. Only the genuine earlier
structural, faithful, Baumann and fixed/A₅-module sources remain.

Source: Aschbacher--Smith 14.7.47--75 and J.1.1.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.SourceConstruction CriticalFusion.SourceConstruction.LocalReduction
open Chapter13.Section03.SourceCompletion
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
  (d : Counterexample T L)
  (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
  (hab : IsMulCommutative F.U)
  (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
  (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
  (fixed : OriginalFixedModule1332At T L)
  (five : OriginalAlternatingFiveModules1332At T L)
include d h hab structural previous faithful earlier fixed five

/-- Construct the original Rudvalis isomorphism with 14.7.47 and Data
supplied internally by the earlier fixed-module source. -/
theorem source_rudvalis_of_original_module_sources_at :
    Nonempty (G ≃* Rudvalis.Model) := by
  obtain ⟨W,add,mod,⟨datum⟩⟩ := exists_data_of_original_fixed_modules_at
    d h hab structural previous faithful earlier fixed
  exact source_rudvalis_from_original_modules_at datum structural faithful five

/-- The same original source application contributes Rudvalis to the full
Theorem D model catalogue. -/
theorem source_theoremDModel_of_original_module_sources_at :
    ClassificationModels.IsTheoremDModel G := by
  exact .exceptional (.sporadic .ru (by simp)
    (source_rudvalis_of_original_module_sources_at
      d h hab structural previous faithful earlier fixed five))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
