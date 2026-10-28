module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralBalance
public import Theory.GroupAction.CubicTree.TrackArcs

/-!
# Equivariant central labels from a fixed track interval

A central element of a vertex stabilizer has a well-defined conjugate at
each vertex of its orbit. Short-arc transitivity then transfers the exact
track interval to the fixed ball and moved sphere at every labeled vertex.
The source application retains the precise distance bound by the first
singularity index and makes no radius restriction.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), following
(6.7), p.399, and the ball argument in (6.9.1), p.400.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem conj_eq_of_same_vertex {v : RankTwo.Vertex F} {z a b : G}
    (hc : ∀g∈RankTwo.stabilizer F v,Commute z g) (he : a • v = b • v) :
    (MulAut.conj a) z = (MulAut.conj b) z := by
  have hk : b⁻¹*a ∈ RankTwo.stabilizer F v := by
    change (b⁻¹*a) • v = v
    rw [mul_smul, he, inv_smul_smul]
  have hz : (b⁻¹*a) * z * (b⁻¹*a)⁻¹ = z := by
    rw [(hc _ hk).symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hh := congrArg (MulAut.conj b) hz
  simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc,
    mul_inv_cancel_left, inv_mul_cancel_left, inv_mul_cancel_right,
    mul_inv_cancel_right, mul_inv_cancel, mul_one] using hh

/-- A central stabilizer element has a well-defined equivariant conjugate
label at every vertex in its orbit. -/
theorem exists_central_orbit_label (v : RankTwo.Vertex F) (z : G)
    (hz : z ∈ RankTwo.stabilizer F v)
    (hc : ∀g∈RankTwo.stabilizer F v,Commute z g) :
    ∃ f : RankTwo.Vertex F → G, f v = z ∧
      (∀ w, w.type = v.type → ∃ g : G, g • v = w ∧ f w = (MulAut.conj g) z) ∧
      (∀ (g : G) w, w.type = v.type → f (g • w) = g * f w * g⁻¹) ∧
      (∀ w, w.type = v.type → f w ∈ RankTwo.stabilizer F w ∧
        ∀g∈RankTwo.stabilizer F w,Commute (f w) g) := by
  classical
  have hex (w : RankTwo.Vertex F) (hw : w.type = v.type) : ∃ g : G, g • v = w :=
    (RankTwo.same_orbit_iff F v w).2 hw.symm
  let rep (w : RankTwo.Vertex F) (hw : w.type = v.type) := (hex w hw).choose
  have hrep (w : RankTwo.Vertex F) (hw : w.type = v.type) : rep w hw • v = w :=
    (hex w hw).choose_spec
  let f : RankTwo.Vertex F → G := fun w => if hw : w.type = v.type then
    (MulAut.conj (rep w hw)) z else 1
  have hf (w : RankTwo.Vertex F) (hw : w.type = v.type) :
      f w = (MulAut.conj (rep w hw)) z := by simp only [f, dif_pos hw]
  have hfe (w : RankTwo.Vertex F) (hw : w.type = v.type) (g : G) (hg : g • v = w) :
      f w = (MulAut.conj g) z := by
    rw [hf w hw]
    exact conj_eq_of_same_vertex hc ((hrep w hw).trans hg.symm)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · simpa only [MulAut.conj_apply, one_mul, inv_one, mul_one] using
      hfe v rfl 1 (one_smul G v)
  · intro w hw
    exact ⟨rep w hw, hrep w hw, hf w hw⟩
  · intro g w hw
    have hgw : (g • w).type = v.type := hw
    rw [hfe (g • w) hgw (g * rep w hw) (by rw [mul_smul, hrep w hw]), hf w hw]
    simp only [MulAut.conj_apply, mul_inv_rev, mul_assoc]
  · intro w hw
    let a := rep w hw
    have ha : a • v = w := hrep w hw
    rw [hf w hw]
    constructor
    · change (a*z*a⁻¹) • w = w
      rw [← ha, mul_smul, mul_smul, inv_smul_smul, hz, ha]
    · intro g hg
      have hk : a⁻¹*g*a ∈ RankTwo.stabilizer F v := by
        change (a⁻¹*g*a) • v = v
        rw [mul_smul, mul_smul, ha, hg, ← ha, inv_smul_smul]
      have hh := (hc _ hk).conj a
      simpa only [MulAut.conj_apply, mul_assoc, mul_inv_cancel_left,
        inv_mul_cancel_right, mul_inv_cancel, mul_one] using hh

/-- Short-arc transitivity identifies fixation at a track point with fixation
at any point at the same distance from the central vertex. -/
theorem CubicTreeAction.central_vertex_fixes_sphere_iff (h : CubicTreeAction F)
    {s : ℕ}
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) (c : ℤ) {z : G}
    (hc : ∀g∈RankTwo.stabilizer F (t.vertex c),Commute z g)
    (w : RankTwo.Vertex F) (hn : (RankTwo.graph F).dist (t.vertex c) w ≤ s) :
    z • w = w ↔ z • t.vertex (c + (RankTwo.graph F).dist (t.vertex c) w) =
      t.vertex (c + (RankTwo.graph F).dist (t.vertex c) w) := by
  let n := (RankTwo.graph F).dist (t.vertex c) w
  let p := t.arc c n
  obtain ⟨q, hq, hend⟩ := BasedWalk.exists_geodesic
    (h.tree.connected.preconnected (t.vertex c) w)
  obtain ⟨g, hg, hmap⟩ := rootPathTransitive_of_short_rightRegular trackGraphAction
    s hshort (t.vertex c) n hn p q (t.arc_nonbacktracking _ _) hq
  have he : g • t.vertex (c+n) = w := by
    simpa only [p, Track.arc_endpoint, hend] using
      endpoint_smul_of_vertices trackGraphAction g p q hmap
  have hgcomm := hc g hg
  constructor
  · intro hz
    apply (MulAction.toPerm g).injective
    change g • (z • t.vertex (c+n)) = g • t.vertex (c+n)
    rw [← mul_smul, hgcomm.symm.eq, mul_smul, he, hz]
  · intro hz
    rw [← he, ← mul_smul, hgcomm.eq, mul_smul, hz]

/-- The exact fixed interval yields the orbit labels and the short-ball/sphere
properties needed by both terminal branches. -/
theorem CubicTreeAction.exists_interval_orbit_labels (h : CubicTreeAction F)
    {s : ℕ}
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z) (c : ℤ) (r : ℕ)
    (hFL : d.fixedLeft = c-(r+1)) (hFR : d.fixedRight = c+(r+1))
    (hc : ∀g∈RankTwo.stabilizer F (t.vertex c),Commute z g) :
    ∃ f : RankTwo.Vertex F → G, f (t.vertex c) = z ∧
      (∀v, v.type = (t.vertex c).type → orderOf (f v) = 2) ∧
      (∀v, v.type = (t.vertex c).type → f v ∈ RankTwo.stabilizer F v ∧
        ∀g∈RankTwo.stabilizer F v,Commute (f v) g) ∧
      (∀(g:G) v, v.type = (t.vertex c).type → f (g • v) = g*f v*g⁻¹) ∧
      (∀v, v.type = (t.vertex c).type → ∀w,
        (RankTwo.graph F).dist v w ≤ r+1 → (RankTwo.graph F).dist v w ≤ s → f v • w = w) ∧
      (∀v, v.type = (t.vertex c).type → r+2 ≤ s → ∀w,
        (RankTwo.graph F).dist v w = r+2 → f v • w ≠ w) := by
  have hzfix : z ∈ RankTwo.stabilizer F (t.vertex c) :=
    (d.fixed_iff c).2 ⟨by omega, by omega⟩
  obtain ⟨f, hf, hrep, hconj, hcentral⟩ := exists_central_orbit_label (t.vertex c) z hzfix hc
  refine ⟨f, hf, ?_, hcentral, hconj, ?_, ?_⟩
  · intro v hv
    obtain ⟨g, _, hg⟩ := hrep v hv
    rw [hg]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z).trans hz.1
  · intro v hv w hdist hs
    obtain ⟨g, hg, hfg⟩ := hrep v hv
    have hd : (RankTwo.graph F).dist (t.vertex c) (g⁻¹ • w) =
        (RankTwo.graph F).dist v w := by
      have hh := trackGraphAction.dist_smul g (t.vertex c) (g⁻¹ • w)
      simpa only [hg, smul_inv_smul] using hh.symm
    have hfix : z • (g⁻¹ • w) = g⁻¹ • w :=
      (h.central_vertex_fixes_sphere_iff hshort t c hc _ (by omega)).2
        ((d.fixed_iff _).2 ⟨by omega, by omega⟩)
    rw [hfg]
    change (g*z*g⁻¹) • w = w
    rw [mul_smul, mul_smul, hfix, smul_inv_smul]
  · intro v hv hs w hdist hfix
    obtain ⟨g, hg, hfg⟩ := hrep v hv
    have hd : (RankTwo.graph F).dist (t.vertex c) (g⁻¹ • w) = r+2 := by
      have hh := trackGraphAction.dist_smul g (t.vertex c) (g⁻¹ • w)
      simpa only [hg, smul_inv_smul, hdist] using hh.symm
    have hzfix' : z • (g⁻¹ • w) = g⁻¹ • w := by
      rw [hfg] at hfix
      have hh := congrArg (g⁻¹ • ·) hfix
      simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using hh
    have hh := (h.central_vertex_fixes_sphere_iff hshort t c hc _ (by omega)).1 hzfix'
    have hi := (d.fixed_iff _).1 hh
    omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
