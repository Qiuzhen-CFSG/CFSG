module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Opposition
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.RootPaths
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.SphereCounts

/-!
# The five point suborbits of the binary Ree building

The original first-parabolic cosets have distance-sphere sizes1,10,80,640,1024.
Rooted nine-path transitivity descends to each sphere, so these are the five
actual point-stabilizer orbits. Both action and incidence metric are retained.
Source: Aschbacher–Smith F.4.6 and J.5.5(2–3), p.446.
-/

public noncomputable section
namespace ReeF4.Octagon.Binary
open Subgroup Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open SimpleGraph.OctagonShortPaths SimpleGraph.PathTransitivePolygon
local instance sphereVertexFintype : Fintype (CosetGeometry.Vertex family) := Fintype.ofFinite _
instance pointCosetMulAction : MulAction (Model 0) PointCoset :=
  @MulAction.quotient (Model 0) (Model 0) inferInstance inferInstance
    (Monoid.toMulAction _) Tits.ExceptionalParabolics.FullRee.first
    (MulAction.left_quotientAction _)

theorem point_sphere_card (u:PointCoset) (i:Fin 5) :
    Nat.card {v:PointCoset // pointDistance u v=2*(i:ℕ)}=
      (![1,10,80,640,1024]:Fin 5→ℕ) i := by
  let E : {v:PointCoset // pointDistance u v=2*(i:ℕ)} ≃
      {v:orderTwoFour.Point // orderTwoFour.pointDistance (cosetPointEquiv u) v=i} :=
    cosetPointEquiv.subtypeEquiv (fun v=>by
      rw [orderTwoFour.pointDistance_eq_iff]; rfl)
  rw [Nat.card_congr E]
  exact orderTwoFour.point_sphere_card _ i

private theorem graph_hasTwoNeighbors : SimpleGraph.BasedWalk.HasTwoNeighbors (graph family) := by
  intro x y
  have hc:1<((graph family).neighborSet x).ncard:=by
    change 1<Nat.card ((graph family).neighborSet x)
    rw [card_neighbors]; split <;> decide
  obtain ⟨a,ha,b,hb,hab⟩:=(Set.one_lt_ncard (Set.toFinite _)).mp hc
  by_cases he:a=y
  · exact ⟨b,hb,fun hh=>hab (he.trans hh.symm)⟩
  · exact ⟨a,ha,he⟩

theorem sphere_transitive (u:CosetGeometry.Vertex family) (n:ℕ) (hn:n≤8) :
    SphereTransitive (graph family) (Model 0) u n := by
  apply ((rootPathTransitive_nine u).mono graph_hasTwoNeighbors (by omega)).sphereTransitive
  · exact ⟨fun a _ _ h=>⟨h.1,h.2.smul family a⟩⟩
  · exact graph_connected

@[simp] theorem pointVertex_smul (g:Model 0) (u:PointCoset) :
    pointVertex (g•u)=g•pointVertex u := rfl

theorem pointVertex_injective : Function.Injective pointVertex := by
  intro u v h
  exact (cosetPointEquiv.injective (Subtype.ext h))

theorem pointDistance_smul (g:Model 0) (u v:PointCoset) :
    pointDistance (g•u) (g•v)=pointDistance u v := by
  change (graph family).dist (g•pointVertex u) (g•pointVertex v)=_
  have hact:GraphAction (graph family) (Model 0):=⟨fun a _ _ h=>⟨h.1,h.2.smul family a⟩⟩
  exact hact.dist_smul g _ _

theorem point_sphere_transitive (u v w:PointCoset)
    (h:pointDistance u v=pointDistance u w) :
    ∃g:Model 0,g•u=u ∧ g•v=w := by
  have hn:pointDistance u v≤8:=graph_dist_le_eight _ _
  obtain ⟨g,hg,hv⟩:=sphere_transitive (pointVertex u) (pointDistance u v) hn
    (pointVertex v) (pointVertex w) rfl h.symm
  exact ⟨g,pointVertex_injective hg,pointVertex_injective hv⟩

end ReeF4.Octagon.Binary
