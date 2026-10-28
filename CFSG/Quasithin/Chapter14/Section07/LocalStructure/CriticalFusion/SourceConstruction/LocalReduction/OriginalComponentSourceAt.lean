module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentRowsAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.ExclusionAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalModuleRows

/-!
# Original 14.7.47 and the actual local data from the earlier fixed-module source

Every actual component has a permitted intrinsic quotient carrier. If its
original point residual were outside, the quotient would be alternating five;
the actual mixed-amalgam argument excludes this using plane movement derived
from the earlier fixed-module theorem. Hence original 14.7.47 holds for all
original local subgroups and their actual C-components. The completed local
row exclusions then construct the original Data.

The structural and fixed-module inputs concern the same original G,T,L.
Neither the component statement, a row exclusion, movement, a chosen module,
nor Data is assumed. Source: Aschbacher--Smith 13.3.2(3),14.7.41--53,
printed pp.885,1061--1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
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
include d h hab structural previous faithful earlier fixed

/-- The original component assertion is constructed on the literal flag,
using only its earlier source inputs. -/
theorem source_14_7_47_of_original_fixed_modules_at : Earlier14747 F L := by
  intro I hI C hC
  refine ⟨?_,local_component_rows_at d h hab structural previous faithful earlier I hI C hC⟩
  by_contra hout
  obtain ⟨e⟩ := local_component_outside_point_is_alternating_five_at
    d h hab structural previous faithful earlier I hI C hC hout
  exact hout (OriginalComponentStatement.OutsideFiveContainment.local_alternating_five_component_contains_point_at
    d h hab structural previous faithful earlier fixed I hI C hC e)

/-- The actual local Data, with 14.7.47 and every local row exclusion proved
from the original source inputs. -/
theorem exists_data_of_original_fixed_modules_at :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  exact OriginalModuleRows.exists_data_of_original_module_sources_at
    d h hab structural previous faithful earlier
    (source_14_7_47_of_original_fixed_modules_at
      d h hab structural previous faithful earlier fixed) fixed

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
