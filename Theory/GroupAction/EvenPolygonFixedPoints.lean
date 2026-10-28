module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Ring.Parity
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.HexagonFixedPoint.TreeCenter

/-!
# Two-local normalizers acting on even generalized polygons

In a bipartite graph of diameter at most `2*d` and girth at least `4*d`,
paths shorter than `2*d` are unique. The vertices fixed by a nonidentity
two-subgroup fixing an edge form a tree when apartment stabilizers have odd
order. The invariant center of this finite tree is fixed by the normalizer;
preservation of the two colors rules out an interchange of its endpoints.

This generalizes the checked hexagon argument in
`Theory/AtlasPort/LinearGroups/G2/EvenLocal/NormalizerCover/HexagonFixedPoint`.
The imported `TreeCenter` module contains only the general finite-tree theorem.
Here `d = 3` gives a hexagon and `d = 4` an octagon. No simplicity or
classification premise is used.

Source: the rank-two building proof of finite Borel--Tits, GLS3 Theorem 3.1.3,
`refs/KGroup/GLS3/chapter3.tex`; the BN-pair geometry is in chapter2, §§2.3, 2.6.
-/

@[expose] public section

open SimpleGraph

namespace GroupAction.EvenPolygon

variable {G X : Type*} [Group G] [MulAction G X]

/-- Vertices fixed by every element of the indicated ambient subgroup. -/
def fixedVertices (R : Subgroup G) : Set X := {x | ∀ r ∈ R, r • x = x}

/-- An action on an even generalized polygon of diameter at most `2*d`.
The stabilizers of apartment cycles have odd order. -/
structure EvenPolygonAction (d : ℕ) (Γ : SimpleGraph X) (color : X → Bool) : Prop where
  adjacent_color : ∀ {x y}, Γ.Adj x y → color x ≠ color y
  smul_adj : ∀ (g : G) {x y}, Γ.Adj x y → Γ.Adj (g • x) (g • y)
  smul_color : ∀ (g : G) (x : X), color (g • x) = color x
  diameter_bound : ∀ x y, ∃ w : Γ.Walk x y, w.length ≤ 2 * d
  cycle_bound : ∀ x (w : Γ.Walk x x), w.IsCycle → 4 * d ≤ w.length
  apartment_stabilizer_odd : ∀ x (w : Γ.Walk x x), w.IsCycle → w.length = 4 * d →
    Odd (Nat.card (fixingSubgroup G {v | v ∈ w.support}))

/-- Normalization, rather than centralization, suffices to preserve the full
fixed vertex set. -/
theorem normalizer_smul_mem_fixedVertices (R : Subgroup G)
    {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G))
    {x : X} (hx : x ∈ fixedVertices R) : g • x ∈ fixedVertices R := by
  intro r hr
  have hc : g⁻¹ * r * g ∈ R := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (R : Set G)).inv_mem hg) r).mp hr
  calc
    r • (g • x) = g • ((g⁻¹ * r * g) • x) := by simp [mul_smul]
    _ = g • x := congrArg (g • ·) (hx _ hc)

/-- A nonidentity two-subgroup cannot fix an apartment cycle pointwise when its
pointwise stabilizer has odd order. -/
theorem not_fixed_apartment [Finite G] {d : ℕ} {Γ : SimpleGraph X} {color : X → Bool}
    (hΓ : EvenPolygonAction (G := G) d Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R)
    (x : X) (w : Γ.Walk x x) (hw : w.IsCycle) (hl : w.length = 4 * d) :
    ¬ ∀ v ∈ w.support, v ∈ fixedVertices R := by
  intro hfix
  have hle : R ≤ fixingSubgroup G {v | v ∈ w.support} := by
    intro r hr
    exact (fun v => hfix v.val v.property r hr)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro h
    apply hR
    apply Subgroup.card_eq_one.mp
    simpa [h] using hn
  have hd : 2 ∣ Nat.card R := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  exact (hΓ.apartment_stabilizer_odd x w hw hl).not_two_dvd_nat
    (hd.trans (Subgroup.card_dvd_of_le hle))

variable {G X : Type*} [Group G] [MulAction G X]
variable {d : ℕ} {Γ : SimpleGraph X} {color : X → Bool}

private theorem short_paths_eq (hΓ : EvenPolygonAction (G := G) d Γ color)
    {x y : X} {p q : Γ.Walk x y} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < (4 * d)) : p = q := by
  by_contra hne
  obtain ⟨z, _, _, c, hc, hlen'⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := hΓ.cycle_bound z c hc
  omega

private theorem walk_color_eq_iff (hΓ : EvenPolygonAction (G := G) d Γ color)
    {x y : X} (p : Γ.Walk x y) : color x = color y ↔ p.length % 2 = 0 := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have hcol := hΓ.adjacent_color h
    simp only [Walk.length_cons]
    cases hx : color x <;> cases hy : color y <;> cases hz : color z <;>
      simp_all <;> omega

/-- A path shorter than half the girth with fixed endpoints is fixed pointwise. -/
theorem short_path_fixed (hΓ : EvenPolygonAction (G := G) d Γ color)
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
    (hΓ : EvenPolygonAction (G := G) d Γ color) (R : Subgroup G)
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

private theorem fixed_graph_cycle_gt [Finite G]
    (hΓ : EvenPolygonAction (G := G) d Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R)
    {x : fixedVertices R} (p : (Γ.induce (fixedVertices R)).Walk x x)
    (hc : p.IsCycle) : (4 * d) < p.length := by
  let f : Γ.induce (fixedVertices R) ↪g Γ := Embedding.induce _
  have hc' : (p.map f.toHom).IsCycle := hc.map f.injective
  have hlen : (p.map f.toHom).length = p.length := Walk.length_map f.toHom p
  have hl : (4 * d) ≤ p.length := calc
    (4 * d) ≤ (p.map f.toHom).length := hΓ.cycle_bound (f x) _ hc'
    _ = p.length := hlen
  by_contra hn
  have heq : (p.map f.toHom).length = (4 * d) := by rw [hlen]; omega
  apply not_fixed_apartment hΓ R hR hp (f x) (p.map f.toHom) hc' heq
  intro v hv
  rw [Walk.support_map, List.mem_map] at hv
  obtain ⟨z, _, rfl⟩ := hv
  exact z.property

private theorem fixed_paths_eq [Finite G]
    (hΓ : EvenPolygonAction (G := G) d Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R)
    {x y : fixedVertices R} {p q : (Γ.induce (fixedVertices R)).Walk x y}
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length + q.length ≤ (4 * d)) : p = q := by
  by_contra hne
  obtain ⟨z, _, _, c, hc, hl⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := fixed_graph_cycle_gt hΓ R hR hpR c hc
  omega

/-- A longer fixed path would give a forbidden fixed apartment by a short fixed shortcut. -/
theorem fixed_path_length_le [Finite G]
    (hΓ : EvenPolygonAction (G := G) d Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R)
    {x y : fixedVertices R} (p : (Γ.induce (fixedVertices R)).Walk x y)
    (hp : p.IsPath) : p.length ≤ 2 * d := by
  by_contra hn
  let q := p.take (2 * d + 1)
  have hlq : q.length = 2 * d + 1 := by simp [q, Walk.take_length]; omega
  have hcol : color x ≠ color (p.getVert (2 * d + 1)) := by
    have he := walk_color_eq_iff hΓ (q.map (Embedding.induce (fixedVertices R)).toHom)
    exact fun h => by
      have hh := he.mp h
      rw [Walk.length_map, hlq] at hh
      omega
  obtain ⟨r, hr, hlr⟩ := exists_short_fixed_path_of_color_ne hΓ R x (p.getVert (2 * d + 1)) hcol
  have heq : q = r := fixed_paths_eq hΓ R hR hpR (hp.take (2 * d + 1)) hr (by omega)
  have := congrArg Walk.length heq
  omega

/-- Odd apartment stabilizers rule out every cycle in the fixed graph. -/
theorem fixed_graph_isAcyclic [Finite G]
    (hΓ : EvenPolygonAction (G := G) d Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R) :
    (Γ.induce (fixedVertices R)).IsAcyclic := by
  intro x c hc
  have hl := fixed_graph_cycle_gt hΓ R hR hpR c hc
  have hmin := hc.three_le_length
  have hp := hc.isPath_take (n := 2 * d + 1) (by omega)
  have := fixed_path_length_le hΓ R hR hpR (c.take (2 * d + 1)) hp
  rw [Walk.take_length] at this
  omega

/-- A fixed edge connects the fixed graph through its two vertex colors. -/
theorem fixed_graph_connected
    (hΓ : EvenPolygonAction (G := G) d Γ color) (R : Subgroup G)
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

/-- The vertices fixed by a nonidentity two-subgroup fixing an edge form a tree. -/
theorem fixed_graph_isTree [Finite G]
    (hΓ : EvenPolygonAction (G := G) d Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R)
    (hedge : ∃ x y, Γ.Adj x y ∧ x ∈ fixedVertices R ∧ y ∈ fixedVertices R) :
    (Γ.induce (fixedVertices R)).IsTree :=
  ⟨fixed_graph_connected hΓ R hedge, fixed_graph_isAcyclic hΓ R hR hpR⟩

variable {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
variable {d : ℕ} {Γ : SimpleGraph X} {color : X → Bool}

/-- In a finite even-polygon action, the normalizer of a nonidentity two-subgroup
fixing an incident pair fixes a vertex. The normalizer need not be a two-group. -/
theorem normalizer_fixed_vertex_of_fixed_edge
    (hΓ : EvenPolygonAction (G := G) d Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R)
    (hedge : ∃ x y, Γ.Adj x y ∧ x ∈ fixedVertices R ∧ y ∈ fixedVertices R) :
    ∃ v : X, ∀ n ∈ Subgroup.normalizer (R : Set G), n • v = v := by
  let T := Γ.induce (fixedVertices R)
  have hT : T.IsTree := fixed_graph_isTree hΓ R hR hpR hedge
  obtain ⟨v, hv⟩ := hT.exists_fixed_vertex_of_color_preserving
    (fun x => color x.val) (fun h => hΓ.adjacent_color h)
  refine ⟨v.val, fun n hn => ?_⟩
  let f : T ≃g T :=
    { toEquiv :=
        { toFun := fun x => ⟨n • x.val, normalizer_smul_mem_fixedVertices R hn x.property⟩
          invFun := fun x => ⟨n⁻¹ • x.val,
            normalizer_smul_mem_fixedVertices R
              ((Subgroup.normalizer (R : Set G)).inv_mem hn) x.property⟩
          left_inv := fun x => Subtype.ext (inv_smul_smul n x.val)
          right_inv := fun x => Subtype.ext (smul_inv_smul n x.val) }
      map_rel_iff' := by
        intro a b
        change Γ.Adj (n • a.val) (n • b.val) ↔ Γ.Adj a.val b.val
        constructor
        · intro h
          simpa only [inv_smul_smul] using hΓ.smul_adj n⁻¹ h
        · exact hΓ.smul_adj n }
  exact congrArg Subtype.val (hv f (fun x => hΓ.smul_color n x.val))

end GroupAction.EvenPolygon
