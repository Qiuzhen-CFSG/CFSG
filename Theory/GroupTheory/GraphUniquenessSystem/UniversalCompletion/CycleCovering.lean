module

public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.CycleTransport
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Coverings trivialized by a normal cycle base

A graph map bijective on neighbor sets gives reversible transport on its vertex
fibers. The transport of the image of a walk recovers that walk's endpoint. If
cycles in a target cycle base have trivial transport, then a connected source
has at most one vertex in each fiber. This is the covering step in the proof
that the target group is the universal completion of its rank-three amalgam.

Source: Aschbacher, *Sporadic Groups* (1994), 35.14–35.16 and 37.5(4).
-/

public section
namespace SimpleGraph.Hom

universe u v
variable {V : Type u} {W : Type v} {Γ : SimpleGraph V} {Δ : SimpleGraph W}
variable (f : Γ →g Δ) (hf : ∀ x, Function.Bijective (f.mapNeighborSet x))

include hf

private theorem lift_unique {x y z : V} (hxy : Γ.Adj x y) (hxz : Γ.Adj x z)
    (h : f y = f z) : y = z :=
  congrArg Subtype.val ((hf x).1 (a₁ := ⟨y, hxy⟩) (a₂ := ⟨z, hxz⟩) (Subtype.ext h))

private theorem exists_liftEdge {u v : W} (h : Δ.Adj u v) (a : {x // f x = u}) :
    ∃ b, Γ.Adj a.val b ∧ f b = v := by
  obtain ⟨b, hb⟩ := (hf a.val).2
    ⟨v, by change Δ.Adj (f a.val) v; simpa only [a.property] using h⟩
  exact ⟨b.val, b.property, congrArg Subtype.val hb⟩

private noncomputable def liftEdge {u v : W} (h : Δ.Adj u v) (a : {x // f x = u}) :
    {x // f x = v} :=
  ⟨(exists_liftEdge f hf h a).choose, (exists_liftEdge f hf h a).choose_spec.2⟩

private theorem liftEdge_adj {u v : W} (h : Δ.Adj u v) (a : {x // f x = u}) :
    Γ.Adj a.val (liftEdge f hf h a).val := (exists_liftEdge f hf h a).choose_spec.1

private theorem liftEdge_backtrack {u v : W} (h : Δ.Adj u v) (a : {x // f x = u}) :
    liftEdge f hf h.symm (liftEdge f hf h a) = a := by
  apply Subtype.ext
  exact lift_unique f hf (liftEdge_adj f hf h.symm (liftEdge f hf h a))
    (liftEdge_adj f hf h a).symm
    ((liftEdge f hf h.symm (liftEdge f hf h a)).property.trans a.property.symm)

/-- A local bijection transports the fiber by lifting each edge. -/
noncomputable def coverTransport : WalkClosure.Transport Δ (fun u => {x // f x = u}) where
  edge h :=
    { toFun := liftEdge f hf h
      invFun := liftEdge f hf h.symm
      left_inv := liftEdge_backtrack f hf h
      right_inv := liftEdge_backtrack f hf h.symm }
  reverse_edge _ := rfl

/-- Lifting the image of an edge recovers the original endpoint. -/
theorem coverTransport_edge {x y : V} (h : Γ.Adj x y) :
    (f.coverTransport hf).edge (f.map_adj h) ⟨x, rfl⟩ = ⟨y, rfl⟩ := by
  apply Subtype.ext
  exact lift_unique f hf (liftEdge_adj f hf (f.map_adj h) ⟨x, rfl⟩) h
    (liftEdge f hf (f.map_adj h) ⟨x, rfl⟩).property

/-- Lifting the image of a walk recovers the original endpoint. -/
theorem coverTransport_walk {x y : V} (p : Γ.Walk x y) :
    (f.coverTransport hf).along (p.map f) ⟨x, rfl⟩ = ⟨y, rfl⟩ := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change (f.coverTransport hf).along (p.map f)
      ((f.coverTransport hf).edge (f.map_adj h) ⟨_, rfl⟩) = _
    rw [f.coverTransport_edge hf h]
    exact ih

/-- Endpoint computation with arbitrary identifications of the image vertices. -/
theorem coverTransport_walk_copy {x y : V} {u v : W} (p : Γ.Walk x y)
    (hx : f x = u) (hy : f y = v) :
    (f.coverTransport hf).along ((p.map f).copy hx hy) ⟨x, hx⟩ = ⟨y, hy⟩ := by
  subst u v
  exact f.coverTransport_walk hf p

/-- If the generating target cycles lift closed, a connected source has singleton
fibers. The hypothesis concerns generators, not all closed walks. -/
theorem injective_of_cycleBase (hΓ : Γ.Preconnected) {S : WalkClosure.Cycles Δ}
    (hbase : WalkClosure.IsCycleBase S)
    (hS : ∀ u (p : Δ.Walk u u), p ∈ S u →
      (f.coverTransport hf).along p = Equiv.refl _) : Function.Injective f := by
  intro x y hxy
  obtain ⟨p⟩ := hΓ x y
  have h₁ := f.coverTransport_walk_copy hf p rfl hxy.symm
  have h₂ := (f.coverTransport hf).along_loop hbase hS ((p.map f).copy rfl hxy.symm)
  have he := congrArg (fun e : {z // f z = f x} ≃ {z // f z = f x} => e ⟨x, rfl⟩) h₂
  exact (congrArg Subtype.val (h₁.symm.trans he)).symm

/-- A nonempty local bijection onto a connected graph is surjective. -/
theorem surjective_of_neighbor_bijective [Nonempty V] (hΔ : Δ.Preconnected) :
    Function.Surjective f := by
  intro y
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨p⟩ := hΔ (f x) y
  exact ⟨((f.coverTransport hf).along p ⟨x, rfl⟩).val,
    ((f.coverTransport hf).along p ⟨x, rfl⟩).property⟩

end SimpleGraph.Hom
