module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Reversal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Transport

/-!
# Failure of the radius natural section in MS93 (4.4.2)

The retained backward critical pair makes Z_(a+2) move modulo Z_a.
If V_a/Z_a had the source's full natural-section structure, its moving
subgroup would lie in the forward span. The radius of the first incident
edge already lies in the forward kernel by critical minimality. Together
these generate V_a, contradicting the supplied escape theorem.

Conjugation transports every field of the actual natural section, including
its quotient marking and triple-commutator clause, to exclude it at any
M-type center. This proves the first implication in the sentence on p.893;
it does not yet prove the subsequent R₂ noncontainment.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893; expanded c notation, printed p.881.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem segment_distance {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.walk.length) :
    (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert j) = j - i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk p.shortest (p.walk.isSubwalk_drop i))
    ((p.walk.drop i).isSubwalk_take (j - i))
  have hmin : j - i ≤ p.walk.length - i := Nat.sub_le_sub_right hj i
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using hh.symm

namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}
  (s : Configuration p) (hb : 4 < geometry.b R)

include s hb source

/-- The retained backward critical path makes its endpoint move at a. -/
theorem second_moving_at_start :
    p.walk.getVert 2 ∈ Escape.movingNeighbors geometry a := by
  apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
    source (by omega) s.delta_color (s.backward_critical hb)
  constructor
  · exact p.dist_start (by have hl := p.length_eq_b; omega)
  · rw [s.distance_start hb, s.distance_second hb]
    omega

/-- The failed forward escape excludes the full expanded c(V_a/Z_a)=1 condition. -/
theorem no_start_radius_naturalSection
    (common : CommonFacts R source geometry)
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    ¬ Nonempty (Escape.NaturalSectionAt a (V R a) (Z R a)) := by
  rintro ⟨n⟩
  have hl := p.length_eq_b
  have hmov : Vcirc R a ≤ localZSpan R (p.walk.getVert 2) a := by
    rw [localZSpan_eq_conjugates]
    exact Escape.Initial.Natural.moving_generation_of_naturalSection
      source geometry (by omega) a p.start_color n _ (s.second_moving_at_start (source := source) hb)
  have hat : Adjacent R a (p.walk.getVert 1) := by
    have hh := p.walk.adj_getVert_succ (i := 0) (by omega)
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj R _ _).mp hh
  have hedge : V R (p.walk.getVert 1) ≤
      Q R (p.walk.getVert (p.walk.length - 2)) := by
    apply Escape.Initial.Consequences.V_le_of_h_neighbors p.start_color hat
    intro d hdt
    have ht : color R (p.walk.getVert 1) = true := by
      have hh := p.vertex_color (i := 1) (by omega)
      cases h : color R (p.walk.getVert 1) <;> simp_all
    have hd : color R d = false := by
      have hn := adjacent_color_ne R hdt
      cases h : color R d <;> simp_all
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d (p.walk.getVert (p.walk.length - 2)) < geometry.b R
    have hnear := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)
    have hfar := segment_distance p (i := 1) (j := p.walk.length - 2) (by omega) (by omega)
    have htri := (cosetGraph_connected R).dist_triangle (u := d)
      (v := p.walk.getVert 1) (w := p.walk.getVert (p.walk.length - 2))
    omega
  have hV : V R a ≤ Q R (p.walk.getVert (p.walk.length - 2)) := by
    rw [Escape.Initial.Consequences.radius_eq_moving_sup_edge source p.start_color hat]
    exact sup_le (hmov.trans hforward) hedge
  exact common.escape a p.start_color a' p.critical _
    (by rw [p.dist_end]; omega)
    (by rw [p.dist_start (Nat.sub_le _ _), ← p.shortest]; omega) hV

/-- Actual vertex conjugation transports the same exclusion to any M-type center. -/
theorem no_radius_naturalSection_at
    (common : CommonFacts R source geometry)
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    {v : Vertex R} (hv : color R v = false) :
    ¬ Nonempty (Escape.NaturalSectionAt v (V R v) (Z R v)) := by
  rintro ⟨n⟩
  obtain ⟨g, hg⟩ := exists_mVertex_of_color R hv
  obtain ⟨h, hh⟩ := exists_mVertex_of_color R p.start_color
  have hmove : act R (g⁻¹ * h) v = a := by
    rw [hg, act_mVertex, mul_inv_cancel_left, ← hh]
  have nt := LocalCommutator.CriticalCase.naturalSectionAt_act (g⁻¹ * h) n
  rw [← V_act, ← Z_act, hmove] at nt
  exact s.no_start_radius_naturalSection hb common hforward ⟨nt⟩

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
