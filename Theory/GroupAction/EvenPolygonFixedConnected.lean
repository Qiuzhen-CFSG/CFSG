module
public import Theory.GroupAction.EvenPolygonFixedPoints

/-!
# Connected fixed graphs from the even-polygon metric

Unique short paths follow from the girth bound. Opposite colors make these
paths shorter than the even diameter, so a fixed edge connects all fixed
vertices. Apartment stabilizers need not have odd order: the fixed graph
may have cycles. This distinction is necessary for even outer extensions.

The proof adapts the metric portion of `EvenPolygonFixedPoints` and is used
by the U₅(4) extension-fusion argument of Aschbacher–Smith F.4.30,35.
-/

public section
open SimpleGraph
namespace GroupAction.EvenPolygon.Metric
variable {G X : Type*} [Group G] [MulAction G X]

/-- Only adjacency and the diameter/girth bounds needed for connectedness. -/
structure MetricAction (d : ℕ) (Γ : SimpleGraph X) (color : X → Bool) : Prop where
  adjacent_color : ∀ {x y}, Γ.Adj x y → color x ≠ color y
  smul_adj : ∀ (g : G) {x y}, Γ.Adj x y → Γ.Adj (g • x) (g • y)
  diameter_bound : ∀ x y, ∃ w : Γ.Walk x y, w.length ≤ 2 * d
  cycle_bound : ∀ x (w : Γ.Walk x x), w.IsCycle → 4 * d ≤ w.length

variable {d : ℕ} {Γ : SimpleGraph X} {color : X → Bool}

private theorem short_paths_eq (hΓ : MetricAction (G := G) d Γ color)
    {x y : X} {p q : Γ.Walk x y} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < (4 * d)) : p = q := by
  by_contra hne
  obtain ⟨z, _, _, c, hc, hlen'⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := hΓ.cycle_bound z c hc
  omega

private theorem walk_color_eq_iff (hΓ : MetricAction (G := G) d Γ color)
    {x y : X} (p : Γ.Walk x y) : color x = color y ↔ p.length % 2 = 0 := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have hcol := hΓ.adjacent_color h
    simp only [Walk.length_cons]
    cases hx : color x <;> cases hy : color y <;> cases hz : color z <;>
      simp_all <;> omega

/-- A path shorter than half the girth with fixed endpoints is fixed pointwise. -/
theorem short_path_fixed (hΓ : MetricAction (G := G) d Γ color)
    (R : Subgroup G) {x y : X} (hx : x ∈ fixedVertices R) (hy : y ∈ fixedVertices R)
    {p : Γ.Walk x y} (hp : p.IsPath) (hlen : p.length < 2 * d) :
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

/-- Oppositely colored fixed vertices have a fixed path shorter than the diameter bound. -/
theorem exists_short_fixed_path_of_color_ne
    (hΓ : MetricAction (G := G) d Γ color) (R : Subgroup G)
    (x y : fixedVertices R) (hcol : color x ≠ color y) :
    ∃ p : (Γ.induce (fixedVertices R)).Walk x y, p.IsPath ∧ p.length < 2 * d := by
  classical
  obtain ⟨w, hw⟩ := hΓ.diameter_bound x y
  let p := w.bypass
  have hp : p.IsPath := w.bypass_isPath
  have hlen : p.length ≤ 2 * d := w.length_bypass_le_length.trans hw
  have hodd : p.length % 2 ≠ 0 := by
    exact fun h => hcol ((walk_color_eq_iff hΓ p).mpr h)
  have hshort : p.length < 2 * d := by omega
  have hfix := short_path_fixed hΓ R x.property y.property hp hshort
  let q := p.induce (fixedVertices R) hfix
  have hmap : q.map (Embedding.induce (fixedVertices R)).toHom = p :=
    by simp [q]
  have hlq : q.length = p.length := by
    rw [← Walk.length_map (Embedding.induce (fixedVertices R)).toHom q, hmap]
    rfl
  refine ⟨q, ?_, by omega⟩
  exact Walk.IsPath.of_map (hmap.symm ▸ hp)

/-- A fixed edge connects the fixed graph through its two vertex colors. -/
theorem fixed_graph_connected
    (hΓ : MetricAction (G := G) d Γ color) (R : Subgroup G)
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


end GroupAction.EvenPolygon.Metric
