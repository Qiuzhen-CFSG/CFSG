module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.ActorEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Backward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable

/-!+# The natural-section branch on source critical orbits

The proved edge identities, local-span cover, forward continuations and backward
displacement give a contradiction for every selected opposite configuration.
An escaping local orbit supplies that selected configuration, with no further
coordinate, centralizer, or generation premise. Thus its actual frame has the
favorable orientation, and the established pairing gives both local clauses.

For a critical prefix, escape is its defining noncontainment. For an endpoint
actor, the separate ActorEscape lemma supplies escape from actual movement.
The full natural-section condition remains the independent input of this
branch; the nonnatural branch has its own source producer.

Source: MS93 (4.4.1)(1), printed pp.890--891.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
open Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R}

/-- The actual edge and local-span theorems select an opposite configuration
whenever the original orbit has proved critical escape. -/
theorem selectedPath_of_spanEscape (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (escape : SpanEscape geometry a c) : Nonempty (SelectedPath R geometry a c) := by
  obtain ⟨s⟩ := edgeData_nonempty common hb ha hc hd hn f hop
  obtain ⟨p⟩ := pathPlacement_of_spanEscape_and_localSpans
    source common hb ha hc hd hn f hop s escape
  exact selectedPath_of_edgeData_and_placement f hop s p

/-- Both continuation arguments now exclude the opposite frame of this orbit. -/
theorem sameOrientation_of_spanEscape (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (escape : SpanEscape geometry a c) : f.SameOrientation := by
  by_contra hop
  obtain ⟨s⟩ := selectedPath_of_spanEscape common hb ha hc hd hn f hop escape
  exact false_of_backward common hb (fun t => t.forwardFacts common hb) s

/-- The natural branch, with critical escape and every pairing premise discharged. -/
theorem localControl_of_naturalSection_and_spanEscape
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (hnat : HasNaturalSection R a c) (escape : SpanEscape geometry a c) :
    LocalControlAt R a c := by
  obtain ⟨f⟩ := frame_nonempty common hc hnat
  exact localControl_of_sameOrientation common ha hc hd hb hn f
    (sameOrientation_of_spanEscape common hb ha hc hd hn f escape)

/-- A genuine source critical prefix discharges the escape premise itself. -/
theorem localControl_of_naturalSection_and_critical_prefix
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a e : Vertex R} (p : CriticalPath R geometry a e)
    (hn : ¬ ⁅Z R a, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2))
    (hnat : HasNaturalSection R a (p.walk.getVert 2)) :
    LocalControlAt R a (p.walk.getVert 2) := by
  have htwo : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  exact localControl_of_naturalSection_and_spanEscape common hb p.start_color
    ((p.vertex_color htwo).mpr (by decide)) (p.dist_start htwo) hn hnat
    (spanEscape_of_critical_prefix p (by omega))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase
