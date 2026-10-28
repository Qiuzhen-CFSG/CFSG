module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationChain
/-!
# Common neighbors of the plane distance-two pairs

The 60 neighbors of each point in a 77-point plane imply that any four plane
points have a common neighbor. Source (5.7) places every common neighbor of
a Δ₁² pair in its unique plane, so its induced common-neighbor graph has
paths of length at most two. This proves precisely (7.5.2), not global
common-neighbor connectedness. The final lemmas identify the actual binary
R₁ relation at distance two and contract its squares in triangle closure.

Source: AS91 (5.3), (5.7), (7.5), pp.600–604.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open SimpleGraph
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

/-- A counting inequality inside one finite plane. -/
theorem plane_intersection_bound {π : Plane z} {A B : Set (Point d.P)}
    (hA : A ⊆ {x | OnPlane d.P x π}) (hB : B ⊆ {x | OnPlane d.P x π}) :
    A.ncard + B.ncard ≤ 77 + (A ∩ B).ncard := by
  have hu : (A ∪ B).ncard ≤ 77 := by
    rw [← d.plane_card π]
    exact Set.ncard_le_ncard (Set.union_subset hA hB)
  have hi := Set.ncard_union_add_ncard_inter A B
  omega

/-- Any four points of a plane have a common neighbor in that plane.
This uses just 77 points and valency 60, not a new rank-three assumption. -/
theorem four_plane_points_common_neighbor {π : Plane z} {a b c e : Point d.P}
    (ha : OnPlane d.P a π) (hb : OnPlane d.P b π)
    (hc : OnPlane d.P c π) (he : OnPlane d.P e π) :
    ∃ w, OnPlane d.P w π ∧ Adj d.L a w ∧ Adj d.L b w ∧ Adj d.L c w ∧ Adj d.L e w := by
  let S := fun x => {w | OnPlane d.P w π ∧ Adj d.L x w}
  have hs (x) : S x ⊆ {w | OnPlane d.P w π} := fun _ h => h.1
  have hab := d.plane_intersection_bound (hs a) (hs b)
  have habc := d.plane_intersection_bound (A := S a ∩ S b) ((Set.inter_subset_left).trans (hs a)) (hs c)
  have habce := d.plane_intersection_bound (A := (S a ∩ S b) ∩ S c)
    ((Set.inter_subset_left).trans ((Set.inter_subset_left).trans (hs a))) (hs e)
  have hca : (S a).ncard = 60 := d.plane_neighbor_card π a ha
  have hcb : (S b).ncard = 60 := d.plane_neighbor_card π b hb
  have hcc : (S c).ncard = 60 := d.plane_neighbor_card π c hc
  have hce : (S e).ncard = 60 := d.plane_neighbor_card π e he
  have hn : 0 < (((S a ∩ S b) ∩ S c) ∩ S e).ncard := by omega
  obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hn)
  exact ⟨w, hw.1.1.1.1, hw.1.1.1.2, hw.1.1.2.2, hw.1.2.2, hw.2.2⟩

/-- AS91 (7.5.2), restricted to the actual Δ₁² pairs. -/
theorem planeDistanceTwo_common_connected {x y : Point d.P}
    (hxy : PlaneDistanceTwo d.L x y) :
    ((graph d.L).commonNeighborGraph x y).Connected := by
  obtain ⟨hd, π, hx, hy⟩ := hxy
  obtain ⟨u, hxu, huy⟩ := hd.2.2
  rw [SimpleGraph.connected_iff]
  constructor
  · intro a b
    have ha := d.common_neighbors_in_plane x y π hd hx hy a.val a.property.1 a.property.2
    have hb := d.common_neighbors_in_plane x y π hd hx hy b.val b.property.1 b.property.2
    obtain ⟨w, _, hxw, hyw, haw, hbw⟩ := d.four_plane_points_common_neighbor hx hy ha hb
    let w' : {w // (graph d.L).Adj x w ∧ (graph d.L).Adj y w} := ⟨w, hxw, hyw⟩
    have haw' : ((graph d.L).commonNeighborGraph x y).Adj a w' := haw
    have hwb' : ((graph d.L).commonNeighborGraph x y).Adj w' b := adj_symm hbw
    exact ⟨.cons haw' hwb'.toWalk⟩
  · exact ⟨⟨u, hxu, adj_symm huy⟩⟩

/-- For the source Δ₁² pairs the specified component is all common neighbors. -/
theorem planeDistanceTwo_component {x y u : Point d.P}
    (hxy : PlaneDistanceTwo d.L x y) (hxu : Adj d.L x u) (huy : Adj d.L u y) :
    commonComponent (graph d.L) x u y = {v | Adj d.L x v ∧ Adj d.L y v} := by
  apply Set.Subset.antisymm (commonComponent_subset _ _ _ _)
  intro v hv
  exact ⟨⟨hxu, adj_symm huy⟩, hv,
    (d.planeDistanceTwo_common_connected hxy).preconnected _ _⟩

/-- The literal binary R₁ relation selects precisely Δ₁² among distance-two pairs. -/
theorem binary_one_iff_planeDistanceTwo {x y : Point d.P} (hxy : DistanceTwo d.L x y) :
    d.binary 1 x y ↔ PlaneDistanceTwo d.L x y := by
  constructor
  · rintro ⟨u, ht⟩
    obtain ⟨π, hx, _, hy⟩ := (d.coplanarStep_iff_plane ht.1 ht.2.1).mp ht.2.2
    exact ⟨hxy, π, hx, hy⟩
  · rintro ⟨_, π, hx, hy⟩
    obtain ⟨u, hxu, huy⟩ := hxy.2.2
    have hu := d.common_neighbors_in_plane x y π hxy hx hy u hxu (adj_symm huy)
    exact ⟨u, hxu, huy, (d.coplanarStep_iff_plane hxu huy).mpr ⟨π, hx, hu, hy⟩⟩

/-- The level-one square contraction for the actual ambient filtration. -/
theorem two_step_related_of_binary_one {x u y v : Point d.P}
    (hxy : d.binary 1 x y) (hxu : (graph d.L).Adj x u) (huy : (graph d.L).Adj u y)
    (hxv : (graph d.L).Adj x v) (hvy : (graph d.L).Adj v y) :
    WalkClosure.Rel (WalkClosure.triangles (graph d.L))
      (.cons hxu huy.toWalk) (.cons hxv hvy.toWalk) := by
  classical
  by_cases he : x = y
  · subst y
    exact ((Walk.TriangleHomotopy.backtrack hxu .nil).trans
      (Walk.TriangleHomotopy.backtrack hxv .nil).symm).toCycleRel
  by_cases ha : (graph d.L).Adj x y
  · exact ((Walk.TriangleHomotopy.triangle hxu huy ha .nil).trans
      (Walk.TriangleHomotopy.triangle hxv hvy ha .nil).symm).toCycleRel
  have hd : DistanceTwo d.L x y := ⟨he, ha, u, hxu, huy⟩
  have hp := (d.binary_one_iff_planeDistanceTwo hd).mp hxy
  apply two_step_related_of_commonComponent (graph d.L) hxu huy hxv hvy
  rw [d.planeDistanceTwo_component hp hxu huy]
  exact ⟨hxv, adj_symm hvy⟩

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
