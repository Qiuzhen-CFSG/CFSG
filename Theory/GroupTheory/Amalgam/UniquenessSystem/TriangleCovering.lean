module

public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleHomotopy

/-!
# Triangle coverings over a simply connected graph

A graph homomorphism that is bijective on neighbor sets and lifts triangles
induces triangle-compatible transport on its vertex fibers. The lift of the
image of a walk recovers its endpoint. Thus contractibility of target loops
forces any two vertices in the same fiber of a preconnected source to coincide.
A nonempty source and a preconnected target also give surjectivity, yielding
an actual graph isomorphism.

This is the graph-covering step in the universal-completion recognition argument.
It does not assume or construct the group completion. The choices of edge lifts
remain private; public transport and endpoint theorems specify their behavior.

Source: Aschbacher, *Sporadic Groups* (1994), 35.16(3) and the proof of 37.5(4).
-/

public section
namespace SimpleGraph
universe u v
variable {V : Type u} {G : SimpleGraph V}
namespace Hom
variable {W : Type v} {H : SimpleGraph W}
/-- A graph covering that also lifts triangles. Local bijectivity alone is not enough
for covering the triangle complex. -/
structure IsTriangleCovering (f : G →g H) : Prop where
  neighbor_bijective : ∀ x, Function.Bijective (f.mapNeighborSet x)
  lift_triangle : ∀ {x y z}, G.Adj x y → G.Adj x z → H.Adj (f y) (f z) → G.Adj y z

namespace IsTriangleCovering
variable {f : G →g H} (C : f.IsTriangleCovering)
include C

/-- Two lifts of an edge from the same vertex have the same endpoint. -/
theorem eq_of_adj_of_image_eq {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z)
    (h : f y = f z) : y = z :=
  congrArg Subtype.val ((C.neighbor_bijective x).1
    (a₁ := ⟨y, hxy⟩) (a₂ := ⟨z, hxz⟩) (Subtype.ext h))

private theorem exists_lift {u v : W} (h : H.Adj u v) (a : {x // f x = u}) :
    ∃ b, G.Adj a.val b ∧ f b = v := by
  obtain ⟨b, hb⟩ := (C.neighbor_bijective a.val).2
    ⟨v, by change H.Adj (f a.val) v; simpa only [a.property] using h⟩
  exact ⟨b.val, b.property, congrArg Subtype.val hb⟩

private noncomputable def lift {u v : W} (h : H.Adj u v) (a : {x // f x = u}) :
    {x // f x = v} :=
  ⟨(C.exists_lift h a).choose, (C.exists_lift h a).choose_spec.2⟩

private theorem lift_adj {u v : W} (h : H.Adj u v) (a : {x // f x = u}) :
    G.Adj a.val (C.lift h a).val := (C.exists_lift h a).choose_spec.1

/-- Lifting edges gives triangle-compatible transport on the fibers. -/
noncomputable def transport : TriangleTransport H (fun u => {x // f x = u}) where
  edge := C.lift
  backtrack h a := by
    apply Subtype.ext
    exact C.eq_of_adj_of_image_eq (C.lift_adj h.symm (C.lift h a))
      (C.lift_adj h a).symm ((C.lift h.symm (C.lift h a)).property.trans a.property.symm)
  triangle hxy hyz hxz a := by
    apply Subtype.ext
    have hac : G.Adj a.val (C.lift hyz (C.lift hxy a)).val :=
      C.lift_triangle (C.lift_adj hxy a).symm (C.lift_adj hyz (C.lift hxy a))
        (by simpa only [a.property, (C.lift hyz (C.lift hxy a)).property] using hxz)
    exact C.eq_of_adj_of_image_eq hac (C.lift_adj hxz a)
      ((C.lift hyz (C.lift hxy a)).property.trans (C.lift hxz a).property.symm)

/-- Transport along the image of an edge recovers its endpoint. -/
theorem transport_edge {x y : V} (h : G.Adj x y) :
    C.transport.edge (f.map_adj h) ⟨x, rfl⟩ = ⟨y, rfl⟩ := by
  apply Subtype.ext
  exact C.eq_of_adj_of_image_eq (C.lift_adj (f.map_adj h) ⟨x, rfl⟩) h
    (C.lift (f.map_adj h) ⟨x, rfl⟩).property

/-- Transport along a mapped walk recovers its endpoint. -/
theorem transport_walk {x y : V} (p : G.Walk x y) :
    C.transport.along (p.map f) ⟨x, rfl⟩ = ⟨y, rfl⟩ := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change C.transport.along (p.map f) (C.transport.edge (f.map_adj h) ⟨_, rfl⟩) = _
    rw [C.transport_edge h]
    exact ih

/-- The endpoint computation also permits identifying either image endpoint. -/
theorem transport_walk_copy {x y : V} {u v : W} (p : G.Walk x y)
    (hx : f x = u) (hy : f y = v) :
    C.transport.along ((p.map f).copy hx hy) ⟨x, hx⟩ = ⟨y, hy⟩ := by
  subst u v
  exact C.transport_walk p

/-- A preconnected triangle covering of a triangle-simply-connected graph is injective. -/
theorem injective (hG : G.Preconnected) (hH : H.TriangleSimplyConnected) :
    Function.Injective f := by
  intro x y hxy
  obtain ⟨p⟩ := hG x y
  have h₁ := C.transport_walk_copy p rfl hxy.symm
  have h₂ := C.transport.along_loop hH ((p.map f).copy rfl hxy.symm) ⟨x, rfl⟩
  exact (congrArg Subtype.val (h₁.symm.trans h₂)).symm

/-- A nonempty covering of a preconnected graph is surjective. -/
theorem surjective [Nonempty V] (hH : H.Preconnected) : Function.Surjective f := by
  intro y
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨p⟩ := hH (f x) y
  exact ⟨(C.transport.along p ⟨x, rfl⟩).val, (C.transport.along p ⟨x, rfl⟩).property⟩

/-- Such a covering is an isomorphism when both graphs are connected and the target
is triangle-simply-connected. -/
noncomputable def toIso [Nonempty V] (hG : G.Preconnected) (hH : H.Preconnected)
    (hs : H.TriangleSimplyConnected) : G ≃g H where
  toEquiv := Equiv.ofBijective f ⟨C.injective hG hs, C.surjective hH⟩
  map_rel_iff' := by
    intro x y
    change H.Adj (f x) (f y) ↔ G.Adj x y
    constructor
    · intro h
      obtain ⟨z, hz⟩ := (C.neighbor_bijective x).2 ⟨f y, h⟩
      have hzy : z.val = y := C.injective hG hs (congrArg Subtype.val hz)
      exact hzy ▸ z.property
    · exact f.map_adj

/-- The covering isomorphism has the original vertex map. -/
theorem toIso_apply [Nonempty V] (hG : G.Preconnected) (hH : H.Preconnected)
    (hs : H.TriangleSimplyConnected) (x : V) : C.toIso hG hH hs x = f x := by
  exact congrFun (Equiv.coe_ofBijective f ⟨C.injective hG hs, C.surjective hH⟩) x

end IsTriangleCovering
end Hom

end SimpleGraph
