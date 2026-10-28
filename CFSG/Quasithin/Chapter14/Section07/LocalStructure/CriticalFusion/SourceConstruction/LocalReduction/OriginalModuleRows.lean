module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.G2ResidualSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource.Exclusion

/-!
# Original local data from the earlier fixed-module source

The original fixed-module clause of 13.3.2 supplies the remaining SL₃
movement argument. The completed A₆, A₇, SL₄ and SL₅ source exclusions
therefore give every row of 14.7.49--51. Original 14.7.52 then supplies
the placement needed by the proved G₂ exclusion, constructing Data.

The earlier structural, faithful, fixed-module and 14.7.47 source inputs
remain explicit. Neither a row exclusion nor Data is assumed.
Source: Aschbacher--Smith 13.3.2, 14.7.47--53 and 14.7.63,
printed pp.884--885,1063--1069.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalModuleRows
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section03.SourceCompletion
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
  (source47 : Earlier14747 F L)
  (fixed : OriginalFixedModule1332At T L)
include d h hab structural previous faithful earlier source47 fixed

/-- Every original local row is excluded using the genuine earlier
fixed-module theorem and the completed source proofs. -/
theorem row_exclusions_of_original_module_sources_at : RowExclusions F L := by
  apply EightSource.row_exclusions_of_linear_three_at
    d h hab structural previous faithful earlier source47
  exact LinearThreeSource.source_14_7_49_linear_three_at
    d h hab structural previous faithful earlier source47 fixed

/-- Construct the actual Data without a row or G₂ exclusion callback. -/
theorem exists_data_of_original_module_sources_at :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  apply G2ResidualSource.exists_data_of_linear_three_at
    d h hab structural previous faithful earlier source47
  exact LinearThreeSource.source_14_7_49_linear_three_at
    d h hab structural previous faithful earlier source47 fixed

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalModuleRows
