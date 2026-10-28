module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic
public import Theory.GroupAction.TypedCosetGeometry
public import Theory.GroupAction.EvenPolygonFixedPoints

/-!
# The full Ree parabolic coset graph

Vertices are typed left cosets of the full root-defined parabolics, including
their complementary tori. Edges mean that the two cosets intersect. Thus a
normalizer-fixed vertex gives the required conjugate containment, with the
inverse coset representative as conjugator. Odd index of the positive fixed
subgroup supplies a fixed edge for every two-subgroup by Sylow conjugacy.

`OctagonGeometry` and `OddApartmentStabilizers` are outstanding concrete
geometric assertions, not certificates containing normalizer coverage. The
existence of a sixteen-cycle already implies properness of both parabolics.
The finite-tree normalizer argument is proved in `EvenPolygonFixedPoints`.

Source: finite Borel--Tits, GLS3 Theorem 3.1.3, and the Ree BN-pair in §§2.3,
2.6 of `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

open Subgroup LargeLocalSeeds ConverseParabolics GroupAction.EvenPolygon
open scoped Pointwise

/-- Typed left cosets of the actual full parabolics. -/
abbrev Vertex (m : ℕ) := CosetGeometry.Vertex (parabolic m)

instance (m : ℕ) : Finite (Vertex m) := by
  let f : Vertex m → (Model m ⧸ parabolic m .suzuki) ⊕
      (Model m ⧸ parabolic m .linear) := fun v =>
    match v with
    | ⟨.suzuki, q⟩ => Sum.inl q
    | ⟨.linear, q⟩ => Sum.inr q
  apply Finite.of_injective f
  rintro ⟨s, q⟩ ⟨t, r⟩ h
  cases s <;> cases t <;> simp_all [f]

/-- The color records which of the two parabolics defines the vertex. -/
def vertexColor {m : ℕ} (v : Vertex m) : Bool :=
  match v.type with
  | .suzuki => false
  | .linear => true

/-- Two vertices are joined when their types differ and their cosets meet. -/
def incidenceGraph (m : ℕ) : SimpleGraph (Vertex m) where
  Adj v w := v.type ≠ w.type ∧ CosetGeometry.Incident (parabolic m) v w
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm _⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem adjacent_color {m : ℕ} {v w : Vertex m}
    (h : (incidenceGraph m).Adj v w) : vertexColor v ≠ vertexColor w := by
  obtain ⟨s, v⟩ := v
  obtain ⟨t, w⟩ := w
  cases s <;> cases t <;> simp_all [incidenceGraph, vertexColor]

theorem smul_adj {m : ℕ} (g : Model m) {v w : Vertex m}
    (h : (incidenceGraph m).Adj v w) :
    (incidenceGraph m).Adj (g • v) (g • w) :=
  ⟨h.1, h.2.smul _ g⟩

@[simp] theorem smul_color {m : ℕ} (g : Model m) (v : Vertex m) :
    vertexColor (g • v) = vertexColor v := rfl

/-- The distance, girth and apartment existence assertions for the concrete
Ree coset graph. No normalizer or simplicity assertion is included. -/
structure OctagonGeometry (m : ℕ) : Prop where
  diameter_bound : ∀ v w : Vertex m,
    ∃ p : (incidenceGraph m).Walk v w, p.length ≤ 8
  cycle_bound : ∀ v (p : (incidenceGraph m).Walk v v), p.IsCycle → 16 ≤ p.length
  apartment_exists : ∃ v, ∃ p : (incidenceGraph m).Walk v v,
    p.IsCycle ∧ p.length = 16

/-- Pointwise apartment stabilizers have odd order. This concerns actual
stabilizers in the coset action, not an unrelated torus of the same order. -/
def OddApartmentStabilizers (m : ℕ) : Prop :=
  ∀ v (p : (incidenceGraph m).Walk v v), p.IsCycle → p.length = 16 →
    Odd (Nat.card (fixingSubgroup (Model m) {w | w ∈ p.support}))

/-- Package the proved action properties with the explicit geometric inputs. -/
theorem OctagonGeometry.toEvenPolygonAction {m : ℕ} (h : OctagonGeometry m)
    (hodd : OddApartmentStabilizers m) :
    EvenPolygonAction (G := Model m) 4 (incidenceGraph m) vertexColor where
  adjacent_color := adjacent_color
  smul_adj := smul_adj
  smul_color := smul_color
  diameter_bound := h.diameter_bound
  cycle_bound := h.cycle_bound
  apartment_stabilizer_odd := hodd

private theorem type_eq_of_two_edges {m : ℕ} {x y z : Vertex m}
    (hxy : (incidenceGraph m).Adj x y) (hyz : (incidenceGraph m).Adj y z) :
    x.type = z.type := by
  have h₁ := hxy.1
  have h₂ := hyz.1
  cases hx : x.type <;> cases hy : y.type <;> cases hz : z.type <;> simp_all

private theorem eq_of_type_of_parabolic_top {m : ℕ} {s : Side}
    (htop : parabolic m s = ⊤) {v w : Vertex m}
    (hv : v.type = s) (hw : w.type = s) : v = w := by
  rcases v with ⟨i, a⟩
  rcases w with ⟨j, b⟩
  dsimp at hv hw
  subst i
  subst j
  have hsub : Subsingleton (Model m ⧸ parabolic m s) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact congrArg (CosetGeometry.Vertex.mk s) (hsub.elim a b)

/-- A sixteen-cycle contains distinct vertices of each type, so neither full
parabolic can be the whole group. -/
theorem OctagonGeometry.parabolic_ne_top {m : ℕ} (h : OctagonGeometry m)
    (s : Side) : parabolic m s ≠ ⊤ := by
  intro htop
  obtain ⟨v, p, hp, hlen⟩ := h.apartment_exists
  have h12 := p.adj_getVert_succ (i := 1) (by omega)
  have h23 := p.adj_getVert_succ (i := 2) (by omega)
  have h34 := p.adj_getVert_succ (i := 3) (by omega)
  have h13 := type_eq_of_two_edges h12 h23
  have h24 := type_eq_of_two_edges h23 h34
  by_cases hs : (p.getVert 1).type = s
  · have he := eq_of_type_of_parabolic_top htop hs (h13.symm.trans hs)
    have := hp.getVert_injOn (show 1 ≤ 1 ∧ 1 ≤ p.length by omega)
      (show 1 ≤ 3 ∧ 3 ≤ p.length by omega) he
    omega
  · have hs' : (p.getVert 2).type = s := by
      have hn := h12.1
      cases h₁ : (p.getVert 1).type <;> cases h₂ : (p.getVert 2).type <;>
        cases s <;> simp_all
    have he := eq_of_type_of_parabolic_top htop hs' (h24.symm.trans hs')
    have := hp.getVert_injOn (show 1 ≤ 2 ∧ 2 ≤ p.length by omega)
      (show 1 ≤ 4 ∧ 4 ≤ p.length by omega) he
    omega

/-- Odd positive index puts every two-subgroup into a conjugate of the positive
fixed subgroup, and hence fixes both vertices of a chamber. -/
theorem exists_fixed_edge {m : ℕ} (hindex : Odd (unipotent m).index)
    (R : Subgroup (Model m)) (hp : IsPGroup 2 R) :
    ∃ v w : Vertex m, (incidenceGraph m).Adj v w ∧
      v ∈ fixedVertices R ∧ w ∈ fixedVertices R := by
  let U : Sylow 2 (Model m) := (unipotent_isPGroup m).toSylow hindex.not_two_dvd_nat
  obtain ⟨S, hRS⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model m) S U
  have hconj : ∀ r ∈ R, g * r * g⁻¹ ∈ unipotent m := by
    intro r hr
    have hm : (MulAut.conj g) r ∈ (MulAut.conj g) • (S : Subgroup (Model m)) :=
      Subgroup.mem_map.mpr ⟨r, hRS hr, rfl⟩
    change g * r * g⁻¹ ∈ (g • S : Sylow 2 (Model m)) at hm
    rw [hg] at hm
    exact hm
  have hfix (s : Side) : g⁻¹ • CosetGeometry.base (parabolic m) s ∈ fixedVertices R := by
    intro r hr
    have hmem : g * r * g⁻¹ ∈ MulAction.stabilizer (Model m)
        (CosetGeometry.base (parabolic m) s) := by
      rw [CosetGeometry.stabilizer_base]
      exact unipotent_le_parabolic m s (hconj r hr)
    have he := MulAction.mem_stabilizer_iff.mp hmem
    calc
      r • (g⁻¹ • CosetGeometry.base (parabolic m) s) =
          g⁻¹ • ((g * r * g⁻¹) • CosetGeometry.base (parabolic m) s) := by
            simp [mul_smul]
      _ = g⁻¹ • CosetGeometry.base (parabolic m) s := congrArg (g⁻¹ • ·) he
  refine ⟨g⁻¹ • CosetGeometry.base (parabolic m) .suzuki,
    g⁻¹ • CosetGeometry.base (parabolic m) .linear, ?_, hfix _, hfix _⟩
  apply smul_adj
  exact ⟨by change Side.suzuki ≠ Side.linear; decide, CosetGeometry.incident_base _ _ _⟩

/-- The inverse representative of a fixed left coset gives the precise
conjugation orientation used by `TwoLocalCover`. -/
theorem normalizer_conjugate_le_of_fixed_vertex {m : ℕ} (R : Subgroup (Model m))
    (v : Vertex m) (hv : ∀ n ∈ normalizer (R : Set (Model m)), n • v = v) :
    ∃ g : Model m, ∃ s : Side,
      (normalizer (R : Set (Model m))).map (MulAut.conj g).toMonoidHom ≤ parabolic m s := by
  obtain ⟨g, hg⟩ := CosetGeometry.exists_smul_base (parabolic m) v
  refine ⟨g⁻¹, v.type, ?_⟩
  rintro x ⟨n, hn, rfl⟩
  have he : (g⁻¹ * n * g) • CosetGeometry.base (parabolic m) v.type =
      CosetGeometry.base (parabolic m) v.type := by
    calc
      _ = g⁻¹ • (n • (g • CosetGeometry.base (parabolic m) v.type)) := by
        simp only [mul_smul]
      _ = g⁻¹ • (g • CosetGeometry.base (parabolic m) v.type) := by
        congr 1
        rw [hg]
        exact hv n hn
      _ = _ := inv_smul_smul g _
  have hm : g⁻¹ * n * g ∈ MulAction.stabilizer (Model m)
      (CosetGeometry.base (parabolic m) v.type) := he
  rw [CosetGeometry.stabilizer_base] at hm
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, inv_inv] using hm

end ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
