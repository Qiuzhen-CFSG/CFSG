module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.TrianglePlanes
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.Triangles
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LineOrbitals

/-!
# Ambient triangle permutations and invariant line labels

The full hexad design group realizes each triangle transposition. Lift it
through the original plane projection and conjugate to the plane containing
an arbitrary ambient triangle. Transpositions generate every permutation
of its three vertices. Uniqueness of the joining lines then transports the
literal native line label from one vertex to another. Plane closure gives
the coplanar labels at each vertex.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.6), p.601.
These use the original point, line and residue data and prove the unchanged
triangle permutation and label clauses of SourceCycleBase.Input.
-/

public section
open Subgroup
open scoped Pointwise Matrix
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

private theorem triangle_swap_base
    (x y u : {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)})
    (hxy : Adj a.L x.val y.val) (hyu : Adj a.L y.val u.val) (hux : Adj a.L u.val x.val) :
    ∃ g : G, g • x.val = x.val ∧ g • y.val = u.val ∧ g • u.val = y.val := by
  obtain ⟨g,hgx,hgy,hgu⟩ := NativeTriangles.swap (a.planePoints x) (a.planePoints y)
    (a.planePoints u) ((a.plane_adj_two x y).mp hxy)
    ((a.plane_adj_two x u).mp (adj_symm hux)) ((a.plane_adj_two y u).mp hyu)
  obtain ⟨c,hc⟩ := a.designProjection_surjective g
  have fix : (c : G) • Cosets.vertex (centralizer z) 1 = Cosets.vertex (centralizer z) 1 := by
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr c.property
  have lift (v w : {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)})
      (hvw : g • (a.planePoints v).val = (a.planePoints w).val) : (c : G) • v.val = w.val := by
    let v' : {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)} :=
      ⟨(c : G) • v.val,by simpa only [OnPlane,fix] using incident_smul (c : G) v.property⟩
    have he : a.planePoints v' = a.planePoints w := by
      apply Subtype.ext
      rw [a.planePoints_equivariant c (a.designProjection c) (a.designProjection_marking c).symm v v' rfl,hc]
      exact hvw
    exact congrArg Subtype.val (a.planePoints.injective he)
  exact ⟨c,lift x x hgx,lift y u hgy,lift u y hgu⟩

/-- Each transposition of an ambient triangle is induced by an actual group
element. The full design group, including its outer coset, supplies the lift. -/
theorem triangle_swap (x y u : Point a.P)
    (hxy : Adj a.L x y) (hyu : Adj a.L y u) (hux : Adj a.L u x) :
    ∃ g : G, g • x = x ∧ g • y = u ∧ g • u = y := by
  obtain ⟨π,hxπ,hyπ,huπ⟩ := a.triangles_in_plane x y u hxy hyu hux
  let r := representative π
  have hp : r⁻¹ • π = Cosets.vertex (centralizer z) 1 := by
    rw [←vertex_representative π,Cosets.smul_vertex,inv_mul_cancel]
  have inc (v : Point a.P) (hv : OnPlane a.P v π) :
      OnPlane a.P (r⁻¹ • v) (Cosets.vertex (centralizer z) 1) := by
    simpa only [OnPlane,hp] using incident_smul r⁻¹ hv
  obtain ⟨g,hgx,hgy,hgu⟩ := a.triangle_swap_base
    ⟨r⁻¹ • x,inc x hxπ⟩ ⟨r⁻¹ • y,inc y hyπ⟩ ⟨r⁻¹ • u,inc u huπ⟩
    (adj_smul r⁻¹ hxy) (adj_smul r⁻¹ hyu) (adj_smul r⁻¹ hux)
  exact ⟨r*g*r⁻¹,by rw [mul_smul,mul_smul,hgx,smul_inv_smul],
    by rw [mul_smul,mul_smul,hgy,smul_inv_smul],
    by rw [mul_smul,mul_smul,hgu,smul_inv_smul]⟩

/-- AS91 (5.6)(2), with the unchanged finite-three permutation convention. -/
theorem triangle_permutations (x y u : Point a.P)
    (hxy : Adj a.L x y) (hyu : Adj a.L y u) (hux : Adj a.L u x)
    (σ : Equiv.Perm (Fin 3)) :
    ∃ g : G, ∀ i : Fin 3, g • (![x,y,u] : Fin 3 → Point a.P) i =
      (![x,y,u] : Fin 3 → Point a.P) (σ i) := by
  obtain ⟨gx,hxx,hxy',hxu⟩ := a.triangle_swap x y u hxy hyu hux
  obtain ⟨gy,hyy,hyu',hyx⟩ := a.triangle_swap y u x hyu hux hxy
  obtain ⟨gu,huu,hux',huy⟩ := a.triangle_swap u x y hux hxy hyu
  have hs (i j : Fin 3) (hne : i ≠ j) : ∃ g : G, ∀ k : Fin 3,
      g • (![x,y,u] : Fin 3 → Point a.P) k =
        (![x,y,u] : Fin 3 → Point a.P) (Equiv.swap i j k) := by
    fin_cases i <;> fin_cases j
    all_goals try exact (hne rfl).elim
    · exact ⟨gu,by intro k; fin_cases k <;> simp [Equiv.swap_apply_def,hux',huy,huu]⟩
    · exact ⟨gy,by intro k; fin_cases k <;> simp [Equiv.swap_apply_def,hyx,hyy,hyu']⟩
    · exact ⟨gu,by intro k; fin_cases k <;> simp [Equiv.swap_apply_def,hux',huy,huu]⟩
    · exact ⟨gx,by intro k; fin_cases k <;> simp [Equiv.swap_apply_def,hxx,hxy',hxu]⟩
    · exact ⟨gy,by intro k; fin_cases k <;> simp [Equiv.swap_apply_def,hyx,hyy,hyu']⟩
    · exact ⟨gx,by intro k; fin_cases k <;> simp [Equiv.swap_apply_def,hxx,hxy',hxu]⟩
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1,by intro i; exact one_smul _ _⟩
  | swap_mul σ i j hij ih =>
    obtain ⟨g,hg⟩ := ih
    obtain ⟨f,hf⟩ := hs i j hij
    exact ⟨f*g,by intro k; rw [mul_smul,hg,hf]; rfl⟩

/-- AS91 (5.6)(3): the same native label is seen at any vertex of a triangle. -/
theorem triangle_labels (x y u : Point a.P) (l m n : Line a.L) (i : Fin 5)
    (hxy : Adj a.L x y) (hyu : Adj a.L y u) (hux : Adj a.L u x)
    (hxl : OnLine a.L x l) (hyl : OnLine a.L y l)
    (hxm : OnLine a.L x m) (hum : OnLine a.L u m)
    (hyn : OnLine a.L y n) (hun : OnLine a.L u n) :
    LineType a.residueChart i x l m ↔ LineType a.residueChart i y l n := by
  obtain ⟨g,hgu,hgx,hgy⟩ := a.triangle_swap u x y hux hxy hyu
  have lines (p q : Point a.P) (h : Adj a.L p q) (j k : Line a.L)
      (haj : OnLine a.L p j) (hbj : OnLine a.L q j)
      (hak : OnLine a.L p k) (hbk : OnLine a.L q k) : j = k := by
    obtain ⟨r,_,hq⟩ := a.unique_line p q h
    exact (hq j ⟨haj,hbj⟩).trans (hq k ⟨hak,hbk⟩).symm
  have hgl : g • l = l := lines x y hxy _ _
    (by simpa only [OnLine,hgy] using incident_smul g hyl)
    (by simpa only [OnLine,hgx] using incident_smul g hxl) hxl hyl
  have hgm : g • m = n := lines y u hyu _ _
    (by simpa only [OnLine,hgx] using incident_smul g hxm)
    (by simpa only [OnLine,hgu] using incident_smul g hum) hyn hun
  constructor
  · intro ht
    simpa only [hgx,hgl,hgm] using lineType_smul g ht
  · intro ht
    have hx' : g⁻¹ • y = x := inv_smul_eq_iff.mpr hgx.symm
    have hl' : g⁻¹ • l = l := inv_smul_eq_iff.mpr hgl.symm
    have hn' : g⁻¹ • n = m := inv_smul_eq_iff.mpr hgm.symm
    simpa only [hx',hl',hn'] using lineType_smul g⁻¹ ht

/-- AS91 (5.6)(1): the lines of a triangle have one of the first three
literal native labels, at each vertex. -/
theorem triangle_coplanar_labels (x y u : Point a.P) (l m : Line a.L)
    (hxy : Adj a.L x y) (hyu : Adj a.L y u) (hux : Adj a.L u x)
    (hxl : OnLine a.L x l) (hyl : OnLine a.L y l)
    (hxm : OnLine a.L x m) (hum : OnLine a.L u m) :
    ∃ i : Fin 5, i.val ≤ 2 ∧ LineType a.residueChart i x l m := by
  obtain ⟨π,hxπ,hyπ,huπ⟩ := a.triangles_in_plane x y u hxy hyu hux
  exact (a.delta_coplanar x l m hxl hxm).mp ⟨π,
    a.plane_closed x y l π hxy.1 hxl hyl hxπ hyπ,
    a.plane_closed x u m π hux.1.symm hxm hum hxπ huπ⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
