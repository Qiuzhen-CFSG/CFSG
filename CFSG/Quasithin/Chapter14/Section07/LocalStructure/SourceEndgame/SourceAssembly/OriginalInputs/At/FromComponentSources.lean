module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalModuleRows
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Assembly

/-!
# Rudvalis after the original local component exclusions

The completed local row arguments construct Data from the original
counterexample, flag and earlier-source interfaces. The existing marked
Steinberg and root-recognition endgame then gives the literal Rudvalis
isomorphism. The earlier fixed-module and A₅ module clauses remain distinct.

This conditional source application retains the genuine Chapter12/13 and
14.7.47 duties; it does not assert classification from proper-K alone.
Source: Aschbacher--Smith 14.7.47--75, printed pp.1063--1078, and J.1.1.
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
  (source47 : WholeResidualAssembly.Earlier14747 F L)
  (fixed : OriginalFixedModule1332At T L)
  (five : OriginalAlternatingFiveModules1332At T L)
include d h hab structural previous faithful earlier source47 fixed five

/-- The actual Rudvalis isomorphism with Data and all row exclusions
constructed from the original earlier-source inputs. -/
theorem source_rudvalis_of_original_component_sources_at :
    Nonempty (G ≃* Rudvalis.Model) := by
  obtain ⟨W,add,mod,⟨datum⟩⟩ := OriginalModuleRows.exists_data_of_original_module_sources_at
    d h hab structural previous faithful earlier source47 fixed
  exact source_rudvalis_from_original_modules_at datum structural faithful five

/-- Feed the constructed original Rudvalis branch into the full D catalogue. -/
theorem source_theoremDModel_of_original_component_sources_at :
    ClassificationModels.IsTheoremDModel G := by
  exact .exceptional (.sporadic .ru (by simp)
    (source_rudvalis_of_original_component_sources_at
      d h hab structural previous faithful earlier source47 fixed five))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
