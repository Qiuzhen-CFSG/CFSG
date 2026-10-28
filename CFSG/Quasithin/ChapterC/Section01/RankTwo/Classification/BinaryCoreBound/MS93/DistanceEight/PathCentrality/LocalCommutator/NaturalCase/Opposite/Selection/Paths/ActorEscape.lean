module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans

/-!+# Critical selection for an orbit that moves an endpoint Z-layer

If x belongs to Z_e and a local orbit moves x, that orbit cannot lie in Q_e:
Q_e centralizes Z_e. When e is b-2 steps from the orbit center, this is exactly
the escape needed by the proved local-span selection. A genuine critical
prefix supplies the same escape directly from its defining noncontainment.

The two applications below retain the original ordered pair, its common
neighbor, and the inverse-conjugated edge in PathPlacement. They do not assert
escape for arbitrary opposite frames. The actor application is used at the
terminal source configuration with e equal to the second critical-path vertex.

Source: MS93 (4.4.1)(1), printed pp.890--891, and the final use of (4.4.1)
in (4.4.4), printed p.894; critical-path notation on printed p.855.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Movement of an actual endpoint element forces escape of this local orbit. -/
theorem spanEscape_of_endpoint_movement {a c e : Vertex R}
    (he : color R e = false)
    (hd : (cosetGraph R).dist c e + 2 = geometry.b R)
    {x : FreeAmalgam R} (hx : x ∈ Z R e)
    (hm : ¬ ⁅localZSpan R a c, zpowers x⁆ ≤ fixedCore R c) :
    SpanEscape geometry a c := by
  refine ⟨e, hd, ?_⟩
  intro h
  apply hm
  have hz : ⁅Q R e, Z R e⁆ = ⊥ := by
    rw [commutator_comm]
    exact geometry.centralizes e he
  exact ((commutator_mono h (zpowers_le.mpr hx)).trans_eq hz).trans bot_le

/-- The source's actual critical prefix already supplies orbit escape. -/
theorem spanEscape_of_critical_prefix {a e : Vertex R}
    (p : CriticalPath R geometry a e) (hb : 2 ≤ geometry.b R) :
    SpanEscape geometry a (p.walk.getVert 2) := by
  refine ⟨e, ?_, ?_⟩
  · rw [p.dist_end, p.length_eq_b]
    omega
  · intro h
    exact p.critical.2 ((Z_le_localZSpan R a (p.walk.getVert 2)).trans h)

variable [Finite M] {source : LocalSource L R}

/-- Perform the selected centralizer placement on a genuine source prefix. -/
theorem pathPlacement_of_critical_prefix (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a e : Vertex R} (p : CriticalPath R geometry a e)
    (hn : ¬ ⁅Z R a, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2))
    (f : FrameAt a (p.walk.getVert 2)) (hop : ¬ f.SameOrientation)
    (s : EdgeData a (p.walk.getVert 2)) :
    Nonempty (PathPlacement geometry a (p.walk.getVert 2) s.neighbor) := by
  have htwo : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  exact pathPlacement_of_spanEscape_and_localSpans source common hb p.start_color
    ((p.vertex_color htwo).mpr (by decide)) (p.dist_start htwo) hn f hop s
    (spanEscape_of_critical_prefix p (by omega))

/-- The actual moving actor discharges the escape input of the placement. -/
theorem pathPlacement_of_endpoint_movement (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c e : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) (s : EdgeData a c)
    (he : color R e = false) (hce : (cosetGraph R).dist c e + 2 = geometry.b R)
    {x : FreeAmalgam R} (hx : x ∈ Z R e)
    (hm : ¬ ⁅localZSpan R a c, zpowers x⁆ ≤ fixedCore R c) :
    Nonempty (PathPlacement geometry a c s.neighbor) :=
  pathPlacement_of_spanEscape_and_localSpans source common hb ha hc hd hn f hop s
    (spanEscape_of_endpoint_movement he hce hx hm)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
