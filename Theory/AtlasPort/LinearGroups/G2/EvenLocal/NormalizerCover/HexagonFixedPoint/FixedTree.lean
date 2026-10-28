module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.HexagonData
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The fixed graph in a generalized hexagon

A nonidentity two-subgroup with a fixed incident pair fixes a tree. Paths of
length below six are unique by the twelve-cycle bound, so their fixed endpoints
force pointwise fixation. Bipartition parity supplies a short path from any fixed
vertex to one endpoint of the fixed edge, giving connectedness.

There are no fixed cycles of length at most twelve: shorter cycles violate the
hexagon bound and twelve-cycles contradict the odd apartment stabilizer. A fixed
simple path of length seven would have a fixed shortcut of length at most five;
the two paths would produce just such a forbidden cycle. Thus every fixed simple
path has length at most six, and a fixed cycle cannot exist.

This is the geometric part of the rank-two Borel--Tits argument used for the
G₂ case in Aschbacher--Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed pp. 3--4 and 481--482. The concrete hexagon and fixed
incident pair remain inputs; this module asserts no model-identification theorem.
-/

@[expose] public section

open SimpleGraph

namespace Atlas.G2.EvenLocal.NormalizerCover

variable {G X : Type*} [Group G] [MulAction G X]
variable {Γ : SimpleGraph X} {color : X → Bool}

private theorem short_paths_eq (hΓ : HexagonData (G := G) Γ color)
    {x y : X} {p q : Γ.Walk x y} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < 12) : p = q := by
  by_contra hne
  obtain ⟨z, _, _, c, hc, hlen'⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := hΓ.cycle_bound z c hc
  omega

private theorem walk_color_eq_iff (hΓ : HexagonData (G := G) Γ color)
    {x y : X} (p : Γ.Walk x y) : color x = color y ↔ p.length % 2 = 0 := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have hcol := hΓ.adjacent_color h
    simp only [Walk.length_cons]
    cases hx : color x <;> cases hy : color y <;> cases hz : color z <;>
      simp_all <;> omega

/-- A path of length below six with fixed endpoints is fixed pointwise. -/
theorem short_path_fixed (hΓ : HexagonData (G := G) Γ color)
    (R : Subgroup G) {x y : X} (hx : x ∈ fixedVertices R) (hy : y ∈ fixedVertices R)
    {p : Γ.Walk x y} (hp : p.IsPath) (hlen : p.length < 6) :
    ∀ v ∈ p.support, v ∈ fixedVertices R := by
  intro v hv r hr
  let f : Γ →g Γ := ⟨(r • ·), fun h => hΓ.smul_adj r h⟩
  let q : Γ.Walk x y := (p.map f).copy (hx r hr) (hy r hr)
  have hq : q.IsPath := by
    apply (Walk.isPath_copy ..).mpr
    exact hp.map (MulAction.injective r)
  have hlenq : q.length = p.length := by simp [q]
  have heq : q = p := short_paths_eq hΓ hq hp (by omega)
  obtain ⟨i, hi, _⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have he := congrArg (fun w : Γ.Walk x y => w.getVert i) heq
  simpa [q, Walk.getVert_map, f, hi] using he


/-- Fixed vertices of opposite colors are joined in the fixed graph by a path
of length at most five. -/
theorem exists_short_fixed_path_of_color_ne
    (hΓ : HexagonData (G := G) Γ color) (R : Subgroup G)
    (x y : fixedVertices R) (hcol : color x ≠ color y) :
    ∃ p : (Γ.induce (fixedVertices R)).Walk x y, p.IsPath ∧ p.length ≤ 5 := by
  classical
  obtain ⟨w, hw⟩ := hΓ.diameter_bound x y
  let p := w.bypass
  have hp : p.IsPath := w.bypass_isPath
  have hlen : p.length ≤ 6 := w.length_bypass_le_length.trans hw
  have hodd : p.length % 2 ≠ 0 := by
    exact fun h => hcol ((walk_color_eq_iff hΓ p).mpr h)
  have hshort : p.length < 6 := by omega
  have hfix := short_path_fixed hΓ R x.property y.property hp hshort
  let q := p.induce (fixedVertices R) hfix
  have hmap : q.map (Embedding.induce (fixedVertices R)).toHom = p :=
    by simp [q]
  have hlq : q.length = p.length := by
    rw [← Walk.length_map (Embedding.induce (fixedVertices R)).toHom q, hmap]
    rfl
  refine ⟨q, ?_, by omega⟩
  exact Walk.IsPath.of_map (hmap.symm ▸ hp)

private theorem fixed_graph_cycle_gt [Finite G]
    (hΓ : HexagonData (G := G) Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R)
    {x : fixedVertices R} (p : (Γ.induce (fixedVertices R)).Walk x x)
    (hc : p.IsCycle) : 12 < p.length := by
  let f : Γ.induce (fixedVertices R) ↪g Γ := Embedding.induce _
  have hc' : (p.map f.toHom).IsCycle := hc.map f.injective
  have hlen : (p.map f.toHom).length = p.length := Walk.length_map f.toHom p
  have hl : 12 ≤ p.length := calc
    12 ≤ (p.map f.toHom).length := hΓ.cycle_bound (f x) _ hc'
    _ = p.length := hlen
  by_contra hn
  have heq : (p.map f.toHom).length = 12 := by rw [hlen]; omega
  apply not_fixed_apartment hΓ R hR hp (f x) (p.map f.toHom) hc' heq
  intro v hv
  rw [Walk.support_map, List.mem_map] at hv
  obtain ⟨z, _, rfl⟩ := hv
  exact z.property

private theorem fixed_paths_eq [Finite G]
    (hΓ : HexagonData (G := G) Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R)
    {x y : fixedVertices R} {p q : (Γ.induce (fixedVertices R)).Walk x y}
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length + q.length ≤ 12) : p = q := by
  by_contra hne
  obtain ⟨z, _, _, c, hc, hl⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := fixed_graph_cycle_gt hΓ R hR hpR c hc
  omega

/-- Every simple path in the fixed graph has length at most six. A seven-edge
prefix would have a fixed shortcut and hence give a forbidden fixed cycle. -/
theorem fixed_path_length_le_six [Finite G]
    (hΓ : HexagonData (G := G) Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R)
    {x y : fixedVertices R} (p : (Γ.induce (fixedVertices R)).Walk x y)
    (hp : p.IsPath) : p.length ≤ 6 := by
  by_contra hn
  let q := p.take 7
  have hlq : q.length = 7 := by simp [q, Walk.take_length]; omega
  have hcol : color x ≠ color (p.getVert 7) := by
    have he := walk_color_eq_iff hΓ (q.map (Embedding.induce (fixedVertices R)).toHom)
    exact fun h => by
      have hh := he.mp h
      rw [Walk.length_map, hlq] at hh
      contradiction
  obtain ⟨r, hr, hlr⟩ := exists_short_fixed_path_of_color_ne hΓ R x (p.getVert 7) hcol
  have heq : q = r := fixed_paths_eq hΓ R hR hpR (hp.take 7) hr (by omega)
  have := congrArg Walk.length heq
  omega

/-- The fixed graph of a nonidentity two-subgroup has no cycles. -/
theorem fixed_graph_isAcyclic [Finite G]
    (hΓ : HexagonData (G := G) Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R) :
    (Γ.induce (fixedVertices R)).IsAcyclic := by
  intro x c hc
  have hl := fixed_graph_cycle_gt hΓ R hR hpR c hc
  have hp := hc.isPath_take (n := 7) (by omega)
  have := fixed_path_length_le_six hΓ R hR hpR (c.take 7) hp
  rw [Walk.take_length] at this
  omega

/-- A fixed incident pair connects the whole fixed graph: each vertex has the
opposite color to one endpoint and is joined to it by a short fixed path. -/
theorem fixed_graph_connected
    (hΓ : HexagonData (G := G) Γ color) (R : Subgroup G)
    (hedge : ∃ x y, Γ.Adj x y ∧ x ∈ fixedVertices R ∧ y ∈ fixedVertices R) :
    (Γ.induce (fixedVertices R)).Connected := by
  obtain ⟨x, y, hxy, hx, hy⟩ := hedge
  let a : fixedVertices R := ⟨x, hx⟩
  let b : fixedVertices R := ⟨y, hy⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨a, fun z => ?_⟩
  by_cases hcol : color x = color z
  · have hcol' : color y ≠ color z := by
      rw [← hcol]
      exact (hΓ.adjacent_color hxy).symm
    obtain ⟨p, _, _⟩ := exists_short_fixed_path_of_color_ne hΓ R b z hcol'
    exact (show (Γ.induce (fixedVertices R)).Adj a b from hxy).reachable.trans p.reachable
  · obtain ⟨p, _, _⟩ := exists_short_fixed_path_of_color_ne hΓ R a z hcol
    exact p.reachable

/-- The vertices fixed by a nonidentity two-subgroup induce a tree when an
incident pair is fixed. If the ambient vertex type is finite, this tree is finite
as well. -/
theorem fixed_graph_isTree [Finite G]
    (hΓ : HexagonData (G := G) Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R)
    (hedge : ∃ x y, Γ.Adj x y ∧ x ∈ fixedVertices R ∧ y ∈ fixedVertices R) :
    (Γ.induce (fixedVertices R)).IsTree :=
  ⟨fixed_graph_connected hΓ R hedge, fixed_graph_isAcyclic hΓ R hR hpR⟩

end Atlas.G2.EvenLocal.NormalizerCover
