module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ShortPaths
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.QuadrangleRecognition

/-!
# The actual binary unitary completion is a quadrangle

Order25920 gives27 plane cosets and72 vertices in total. The ten rooted
nonbacktracking two-walks cannot cover all other plane cosets, so there is a
vertex at distance four. Five-path transitivity makes the80 rooted four-walks
geodesic, and their endpoints in72 vertices cannot all be distinct. The metric
recognition theorem then proves girth eight and diameter four.

Source: Aschbacher–Smith F.4.6, F.4.8 andF.4.24, printed pp.276–287.
-/
public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open QuadrangleRecognition
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

theorem quadrangle_metric (hcard : Nat.card G = 25920) :
    (∀ v (p : c.graph.Walk v v),p.IsCycle → 8 ≤ p.length) ∧
    (∀ v w,c.graph.dist v w ≤ 4) ∧
    (∃ v,∃ p : c.graph.Walk v v,p.IsCycle ∧ p.length = 8) := by
  let x : c.Point := ⟨RankTwo.base c.family true,rfl⟩
  have : Finite {p : BasedWalk c.graph 2 x.val // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [c.card_two_paths x]; decide)
  have hcolor : ∀ {u v : c.Vertex},c.graph.Adj u v → u.type ≠ v.type := fun h => h.1
  have hfar := exists_distance_four_of_card c.connected (·.type) hcolor x.val
    (by change 1 + Nat.card {p : BasedWalk c.graph 2 x.val // p.Nonbacktracking} < Nat.card c.Point
        rw [c.card_two_paths x,c.card_point hcard]; decide)
  obtain ⟨y,hy⟩ := hfar
  have horbit : ∀ {v w : c.Vertex},v.type = w.type → ∃ g : G,g • v = w :=
    fun h => (RankTwo.same_orbit_iff c.family _ _).mpr h
  have hgeo : ∀ p : BasedWalk c.graph 4 x.val,p.Nonbacktracking → c.graph.dist x.val p.endpoint = 4 :=
    fun p hp => short_geodesic_on_orbit c.graphAction c.connected c.hasTwoNeighbors
      c.five_transitive (·.type) horbit hy rfl le_rfl p hp
  obtain ⟨z,hz,p,q,hp,hq,hpq⟩ := small_of_four_path_card hgeo
    (by rw [c.card_vertex hcard,c.card_four_paths x]; decide)
  exact quadrangle_of_small c.graphAction c.connected c.hasTwoNeighbors c.five_transitive
    (·.type) hcolor horbit ⟨x.val,z,hz,p,q,hp,hq,hpq⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
