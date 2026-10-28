module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Complete
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Consumers

/-!
# The complete point-core source theorem in its original consumers

The complete catalogue proof supplies V ≤ O₂(G₁) without LocalComponents.
Apply it to the original elementary-span, point-control, first-closure,
generation-one and terminal implications, preserving the marking and all
ambient maps. Their only remaining local premises are the two general
normalizer containments, still owned by qt-d-1251-local.

Structural1222At retains its earlier producer qt-d-1222-source. The terminal
configuration remains with qt-d-1251-fusion; qt-d-1251-source discharges the
earlier inputs in final exterior assembly.
Source: Aschbacher--Smith 12.5.8--11 and the proof of 12.5.1, pp.820--822.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M)

include h structural hG₃ hG₆

/-- Both point-core clauses with the core premise discharged from the source. -/
theorem point_core_and_elementary_span_from_source :
    V ≤ (s.marking.Gi 1).pCoreIn 2 ∧ IsElementaryAbelian 2 s.marking.U :=
  ⟨s.seed_le_point_core_from_source h,
    elementary_point_span_of_source_parameters s h structural hG₃ hG₆
      (s.seed_le_point_core_from_source h)⟩

/-- Original point control no longer requires an assumed component refinement. -/
theorem pointControl_from_local_source : PointControl s.marking :=
  pointControl_of_source_parameters s h structural hG₃ hG₆
    (s.seed_le_point_core_from_source h)

/-- The first weak closure centralizes the original six-space. -/
theorem first_centralizes_V₆_from_local_source :
    ChapterE.indexedWeakClosure V (T : Subgroup G) 1 ≤
      centralizer (s.marking.Vi 6 : Set G) :=
  first_centralizes_V₆_of_source_parameters s h structural hG₃ hG₆
    (s.seed_le_point_core_from_source h)

/-- The genuine generation-one exclusion with point-core containment proved. -/
theorem generation_ne_one_from_local_source
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ChapterE.generationParameter H ≠ 1 :=
  generation_ne_one_of_source_parameters s h structural hG₃ hG₆
    (s.seed_le_point_core_from_source h) hH

/-- The unchanged terminal implication with its point-core premise discharged. -/
theorem exterior_contradiction_from_local_source_and_terminal
    (d : TerminalConfiguration s.marking) : False :=
  exterior_contradiction_of_source_parameters_and_terminal s h structural hG₃ hG₆
    (s.seed_le_point_core_from_source h) d

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
