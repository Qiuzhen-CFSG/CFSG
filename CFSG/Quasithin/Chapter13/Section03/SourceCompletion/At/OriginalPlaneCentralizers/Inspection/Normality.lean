module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Normality
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Extraction
/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.Inspection.Normality`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- C.2.7's actual star catalogue supplies a cubic in J/O₂(J), so the second
cubic in N_G(A) forces the original component to be normal in N_G(A). -/
theorem Context.local_component_normalizer (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) :
    normalizer (d.A : Set G) ≤ normalizer (J : Set G) := by
  let := j.input.quasisimple
  exact s.plane_component_normalizes_of_three_dvd d j.input.component
    (ChapterC.C27Source.coreQuotient_three_dvd_from_source j.input)

/-- The normality required by the later C.2.7 parabolic geometry is relative
to the literal centralizer, and follows from the original local input. -/
theorem Context.local_component_normal (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) :
    (J.subgroupOf (centralizer (d.A : Set G))).Normal :=
  normal_subgroupOf_of_le_normalizer ((Subgroup.centralizer_le_normalizer _).trans
    (s.local_component_normalizer d J j))
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
