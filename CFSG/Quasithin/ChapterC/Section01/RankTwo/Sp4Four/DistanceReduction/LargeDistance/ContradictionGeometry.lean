module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.CentralPropagation

/-!
# Radius commutations for the large-distance source argument

Critical-distance minimality makes a seed centralize a nearby radius group.
Applying this twice controls two nearby radius groups when b>6. The actual
critical commutators therefore centralize the radius groups used on p924,
without assuming any source natural-action conclusion.

Source: MS93 (5.11), printed p924. Vertices and distances are explicit:
this file does not rely on the ambiguous subscript in the printed R-definition.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
variable {M : Type*} [Group M] {R : Subgroup M} (geometry : Geometry R)

theorem seed_centralizes_radius_of_distance {a c : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c + 2 < geometry.b R) :
    Z R a ≤ centralizer (V R c : Set (FreeAmalgam R)) := by
  apply le_centralizer_iff.mpr
  apply (V_le_iff R hc _).mpr
  intro d hdc hdist
  have hQ : Z R d ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdc)
    rw [geometry.distance_constant d hdc]
    change (cosetGraph R).dist d a < geometry.b R
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := c) (w := a)
    rw [SimpleGraph.dist_comm (u := c) (v := a)] at htri
    omega
  exact hQ.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)))

theorem radius_centralizes_radius_of_distance {a c : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c + 4 < geometry.b R) :
    V R a ≤ centralizer (V R c : Set (FreeAmalgam R)) := by
  apply (V_le_iff R ha _).mpr
  intro d hdc hdist
  apply seed_centralizes_radius_of_distance geometry hdc hc
  have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := c)
  omega

theorem nearby_radius_centralizes_of_six_lt (hb : 6 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2) :
    V R a ≤ centralizer (V R c : Set (FreeAmalgam R)) :=
  radius_centralizes_radius_of_distance geometry ha hc (by omega)

theorem seed_commutator_le_second_of_distance {a e : Vertex R}
    (ha : color R a = false) (hd : (cosetGraph R).dist a e ≤ geometry.b R) :
    ⁅Z R a,Z R e⁆ ≤ Z R e := by
  apply le_normalizer_iff_commutator_le_right.mp
  apply le_trans _ (Z_normalized R e)
  apply Z_le_stabilizer_of_dist_le a (geometry.exists_critical a ha)
  rwa [geometry.distance_constant a ha]

theorem seed_commutator_centralizes_radius {a e c : Vertex R}
    (ha : color R a = false) (he : color R e = false) (hc : color R c = false)
    (hae : (cosetGraph R).dist a e ≤ geometry.b R)
    (hec : (cosetGraph R).dist e c + 2 < geometry.b R) :
    ⁅⁅Z R a,Z R e⁆,V R c⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact (seed_commutator_le_second_of_distance geometry ha hae).trans
    (seed_centralizes_radius_of_distance geometry he hc hec)

theorem two_critical_commutators_centralize_radius (hb : 4 < geometry.b R)
    {a d e f c : Vertex R}
    (p : CriticalPath R geometry a e) (q : CriticalPath R geometry d f)
    (hc : color R c = false)
    (hec : (cosetGraph R).dist e c ≤ 2)
    (hfc : (cosetGraph R).dist f c ≤ 2) :
    ⁅⁅Z R a,Z R e⁆ ⊔ ⁅Z R d,Z R f⁆,V R c⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply sup_le
  · apply commutator_eq_bot_iff_le_centralizer.mp
    apply seed_commutator_centralizes_radius geometry p.start_color p.end_color hc
    · exact p.shortest.symm.trans p.length_eq_b |>.le
    · omega
  · apply commutator_eq_bot_iff_le_centralizer.mp
    apply seed_commutator_centralizes_radius geometry q.start_color q.end_color hc
    · exact q.shortest.symm.trans q.length_eq_b |>.le
    · omega

theorem critical_radius_intersection_commutator_centralizes (hb : 6 < geometry.b R)
    {d e c : Vertex R} (p : CriticalPath R geometry d e) (hc : color R c = false)
    (hec : (cosetGraph R).dist e c ≤ 2)
    (A : Subgroup (FreeAmalgam R)) :
    ⁅⁅Z R d,V R e ⊓ A⁆,V R c⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  have hn : Z R d ≤ stabilizer R e :=
    Z_le_stabilizer_of_dist_le d (geometry.exists_critical d p.start_color) p.critical.1.le
  have hle : ⁅Z R d,V R e ⊓ A⁆ ≤ V R e :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp
        (hn.trans (DistanceEight.V_normalized R e)))
  exact hle.trans (nearby_radius_centralizes_of_six_lt geometry hb p.end_color hc hec)

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
