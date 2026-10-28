module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.PlaneMovementAt.Exclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.FullPointCentralizerAt

/-!
# Original plane movement before the component statement

Under contrary centrality, the original fixed-module theorem excludes point
containment in every full-point component. The faithful small-component list
and the binary linear-three containment theorem leave only outside A₅ components.
They centralize the point image, so generalized Fitting self-centralization
makes that image normal. Original point-core geometry gives the contradiction.
All actors, sections, points and cores are the original ones. The input is the
actual earlier fixed-module clause at the same G,T,L; no later component
statement, module choice, plane-movement premise or Data record is supplied.
Source: Aschbacher–Smith 13.3.2(3),13.3.14,14.3.4,14.7.4, printed pp.885,893,990,1043.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.PlaneMovementAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter12.Section02 Chapter13.Section03.SourceCompletion
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original fixed-module source forces movement by the full point core,
without a later component statement or a selected module premise. -/
theorem original_plane_moved_of_fixed_module_source_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (fixed : OriginalFixedModule1332At T L) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  intro hc
  have hall := all_components_outside_five_of_plane_centralized_at
    d h hab structural previous faithful earlier fixed hc
  have hn := local_point_normal_of_all_components_outside_five_at
    d h hab structural previous faithful earlier hall
  exact plane_moved_of_point_normal_at h structural hn hc

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.PlaneMovementAt
