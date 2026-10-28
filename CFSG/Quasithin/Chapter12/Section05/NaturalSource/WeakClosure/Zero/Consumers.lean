module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.First.Geometry

/-!
# Source parameters in the exterior classification consumers

The proved 12.5.6--7 statements supply the actual numerical and zeroth
weak-closure inputs on the original chosen module. Together with the
independent point-core containment they make the point span elementary,
construct point control, and discharge the first-closure geometry inputs.
The resulting W₁ bound and W₀-normalizer bound exclude generation one for
the original H-star family. The terminal commutator argument is also
applied with its point-control premise now proved.

Structural1222At remains the authorized earlier input from
qt-d-1222-source. The original G₃,G₆ containments and point-core containment
are owned by qt-d-1251-local. The terminal configuration and the outer
12.5.1/classification assembly remain with qt-d-1251-fusion; no existence
of that configuration is asserted here.

Source: Aschbacher--Smith, 12.5.6--11 and the proof of 12.5.1,
printed pp.819--822.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The literal point span is elementary once the independent point-core
input is supplied; the zeroth weak-closure premise is now proved. -/
theorem elementary_point_span_of_source_parameters (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2) :
    IsElementaryAbelian 2 s.marking.U :=
  elementary_point_span s hcore
    (zero_clauses_of_source_parameters s h structural hG₃ hG₆).1

/-- Apply the first-closure calculation with its numerical, point-fusion
and elementary-span inputs all constructed on the unchanged marking. -/
theorem first_centralizes_V₆_of_source_parameters (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2) :
    indexedWeakClosure V (T : Subgroup G) 1 ≤
      centralizer (s.marking.Vi 6 : Set G) := by
  let := D.elementary
  obtain ⟨hr, _, hs⟩ := s.source_parameters h structural hG₃ hG₆
  let : IsElementaryAbelian 2 s.marking.U :=
    elementary_point_span_of_source_parameters s h structural hG₃ hG₆ hcore
  exact first_centralizes_V₆ s
    (pointControl_of_source_parameters s h structural hG₃ hG₆ hcore) hr hs

/-- The literal H-star generation consumer with no numerical or weak-closure
premise remaining. The point-core input is the independent local 12.5.8(1). -/
theorem generation_ne_one_of_source_parameters (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    generationParameter H ≠ 1 := by
  let := D.elementary
  obtain ⟨hr, _, hs⟩ := s.source_parameters h structural hG₃ hG₆
  exact generation_ne_one_of_parameters s h structural hG₆ hr hs
    (first_centralizes_V₆_of_source_parameters s h structural hG₃ hG₆ hcore) hH

/-- Apply the proved source parameters and point fusion to the actual terminal
commutator argument. Its configuration remains with the outer assembly owner. -/
theorem exterior_contradiction_of_source_parameters_and_terminal
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2)
    (d : TerminalConfiguration s.marking) : False :=
  exterior_contradiction_of_point_and_terminal s.marking
    (pointControl_of_source_parameters s h structural hG₃ hG₆ hcore) d

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
