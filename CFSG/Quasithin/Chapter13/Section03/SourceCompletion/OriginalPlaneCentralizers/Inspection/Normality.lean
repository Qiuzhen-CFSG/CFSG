module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.CubicOrder
/-!
# Normality of the original plane component before inspection

The genuine C.2.7 star catalogue supplies a cubic in the literal quotient
J/O₂(J). The second cubic in N_G(A) outside C_G(A) then forces J to be
normal in the whole plane normalizer. Restricting gives exactly the relative
normality used by the later C.2.7 parabolic geometry.

Source: Aschbacher--Smith 13.3.12, printed p.889, and1.2.1--2, pp.504--505.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
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
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
