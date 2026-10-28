module

public import Theory.GroupAction.RankTwoCosetGeometry.Distance
public import Theory.GroupAction.DihedralPolygon.Geodesics
public import Theory.Combinatorics.RegularConfiguration
public import Theory.Combinatorics.RegularConfigurationConfig
public import Theory.Combinatorics.CollineationAction

/-!
# Projective planes on the two fibers of a coset graph

A connected rank-two coset graph of diameter at most three, with unique
geodesics below length three and constant valence `q + 1`, is the incidence
graph of a projective plane of order `q` when `q > 1`. Points are the false
fiber, lines the true fiber, and membership is the original adjacency.

Distinct vertices of the same type have distance two and a unique common
neighbor. Counting the length-two branches gives `q² + q + 1` vertices of
each type. The regular-configuration lemmas then provide the plane axioms.
The original group acts by collineations on these exact fibers.

Source: the generalized-triangle case of Aschbacher–Smith F.4.8,
printed pp.278–282; the elementary incidence-count argument is independent
of Lie-group recognition.
-/

@[expose] public section

open Configuration
namespace Subgroup.CosetGeometry.RankTwo
noncomputable section
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

abbrev Fiber (i : Bool) := {v : Vertex F // v.type = i}

/-- The fiber is the literal coset space of its marked subgroup. -/
def fiberEquivQuotient (i : Bool) : Fiber F i ≃ G ⧸ F i where
  toFun v := v.property ▸ v.val.coset
  invFun q := ⟨⟨i, q⟩, rfl⟩
  left_inv v := by
    rcases v with ⟨⟨j, q⟩, h⟩
    dsimp only at h
    subst j
    rfl

instance finiteVertex [Finite G] : Finite (Vertex F) :=
  Finite.of_equiv _ (vertexEquivSum F).symm

instance fiberMulAction (i : Bool) : MulAction G (Fiber F i) where
  smul g v := ⟨g • v.val, v.property⟩
  one_smul v := Subtype.ext (one_smul G v.val)
  mul_smul g h v := Subtype.ext (mul_smul g h v.val)

@[simp] theorem fiber_smul_val (i : Bool) (g : G) (v : Fiber F i) :
    (g • v).val = g • v.val := rfl

abbrev Point := Fiber F false
abbrev Line := Fiber F true

instance pointLineMembership : Membership (Point F) (Line F) :=
  ⟨fun l p => (graph F).Adj p.val l.val⟩

@[simp] theorem point_mem_line (p : Point F) (l : Line F) :
    p ∈ l ↔ (graph F).Adj p.val l.val := Iff.rfl

instance collineationAction : IsCollineationAction G (Point F) (Line F) where
  smul_mem_smul_iff g _p _l := (translationGraphIso F g).map_rel_iff

private theorem two_step_type {v w z : Vertex F}
    (hvw : (graph F).Adj v w) (hwz : (graph F).Adj w z) : v.type = z.type := by
  have h₁ := hvw.1
  have h₂ := hwz.1
  cases hv : v.type <;> cases hw : w.type <;> cases hz : z.type <;> simp_all

variable (hg : F false ⊔ F true = ⊤)
  (hu : (graph F).UniqueGeodesicsBelow 3)
  (hd : ∀ v w, (graph F).dist v w ≤ 3)

include hg hd in
private theorem dist_same_type {v w : Vertex F} (ht : v.type = w.type) (hne : v ≠ w) :
    (graph F).dist v w = 2 := by
  have he := (even_dist_iff F hg v w).mpr ht
  have hpos := (connected F hg).pos_dist_of_ne hne
  have hle := hd v w
  obtain ⟨k, hk⟩ := he
  omega

include hg hu hd

/-- Two distinct vertices of one type have exactly one common neighbor. -/
theorem existsUnique_commonNeighbor_of_plane_geometry {v w : Vertex F}
    (ht : v.type = w.type) (hne : v ≠ w) :
    ∃! z : Vertex F, (graph F).Adj v z ∧ (graph F).Adj w z := by
  have he := dist_same_type F hg hd ht hne
  have he' : (graph F).edist v w = 2 := by
    rw [← ((connected F hg) v w).coe_dist_eq_edist, he]
    rfl
  obtain ⟨z, hz⟩ := (SimpleGraph.edist_eq_two_iff.mp he').2.2
  refine ⟨z, hz, ?_⟩
  intro t ht
  let p : (graph F).Walk v w := .cons ht.1 (.cons ht.2.symm .nil)
  let q : (graph F).Walk v w := .cons hz.1 (.cons hz.2.symm .nil)
  have hpq := hu p q (by change 2 = _; exact he.symm)
    (by change 2 = _; exact he.symm) (by omega)
  exact congrArg (fun r : (graph F).Walk v w => r.getVert 1) hpq

variable [Finite G]

/-- Counting length-two branches gives the exact size of each type fiber. -/
theorem card_fiber_of_plane_geometry (q : ℕ)
    (hv : ∀ v, Nat.card ((graph F).neighborSet v) = q + 1) (i : Bool) :
    Nat.card (Fiber F i) = q ^ 2 + q + 1 := by
  classical
  let : Fintype (Vertex F) := Fintype.ofFinite _
  let v := base F i
  let T := Σ w : (graph F).neighborSet v,
    {z : (graph F).neighborSet w.val // z.val ≠ v}
  let U := {z : Fiber F i // z.val ≠ v}
  let f : T → U := fun t => ⟨⟨t.2.val.val,
    (two_step_type F t.1.property t.2.val.property).symm⟩, t.2.property⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      have hz : a.2.val.val = b.2.val.val := congrArg (fun t : U => t.val.val) hab
      have hw : a.1 = b.1 := by
        apply Subtype.ext
        obtain ⟨w, _, hw⟩ := existsUnique_commonNeighbor_of_plane_geometry F hg hu hd
          (two_step_type F a.1.property a.2.val.property) a.2.property.symm
        exact (hw a.1 ⟨a.1.property, a.2.val.property.symm⟩).trans
          (hw b.1 ⟨b.1.property, hz.symm ▸ b.2.val.property.symm⟩).symm
      cases a with | mk a₁ a₂ =>
        cases b with | mk b₁ b₂ =>
          dsimp only at hw
          subst b₁
          congr 1
          exact Subtype.ext (Subtype.ext hz)
    · intro z
      obtain ⟨w, hw, _⟩ := existsUnique_commonNeighbor_of_plane_geometry F hg hu hd
        z.val.property.symm z.property.symm
      exact ⟨⟨⟨w, hw.1⟩, ⟨⟨z.val.val, hw.2.symm⟩, z.property⟩⟩, rfl⟩
  have hT : Nat.card T = (q + 1) * q := by
    rw [show Nat.card T = ∑ w : (graph F).neighborSet v,
      Nat.card {z : (graph F).neighborSet w.val // z.val ≠ v} from Nat.card_sigma]
    have hr (w : (graph F).neighborSet v) :
        Nat.card {z : (graph F).neighborSet w.val // z.val ≠ v} = q := by
      let a : (graph F).neighborSet w.val := ⟨v, (show (graph F).Adj v w.val from w.property).symm⟩
      have hh : {z : (graph F).neighborSet w.val // z.val ≠ v} =
          {z : (graph F).neighborSet w.val // z ≠ a} := by
        congr 1
        ext z
        exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      rw [hh, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hv]
      omega
    simp_rw [hr]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card, hv]
  have hU : Nat.card U = Nat.card (Fiber F i) - 1 := by
    let a : Fiber F i := ⟨v, rfl⟩
    have hh : U = {z : Fiber F i // z ≠ a} := by
      dsimp only [U]
      congr 1
      ext z
      exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [hh, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]
  have heq := Nat.card_congr (Equiv.ofBijective f hbij)
  rw [hT, hU] at heq
  have hpos : 0 < Nat.card (Fiber F i) := by
    exact Nat.card_pos_iff.mpr ⟨⟨⟨v, rfl⟩⟩, inferInstance⟩
  have hsucc := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  nlinarith

omit hg hu hd

/-- The incidence points on a line are exactly its graph neighbors. -/
def pointsOnLineEquivNeighbors (l : Line F) :
    {p : Point F // p ∈ l} ≃ (graph F).neighborSet l.val where
  toFun p := ⟨p.val.val, p.property.symm⟩
  invFun p := ⟨⟨p.val, by
    have h := p.property.1
    rw [l.property] at h
    cases hp : p.val.type <;> simp_all⟩, p.property.symm⟩

/-- The pencil at a point is exactly its graph neighborhood. -/
def linesOnPointEquivNeighbors (p : Point F) :
    {l : Line F // p ∈ l} ≃ (graph F).neighborSet p.val where
  toFun l := ⟨l.val.val, l.property⟩
  invFun l := ⟨⟨l.val, by
    have h := l.property.1
    rw [p.property] at h
    cases hl : l.val.type <;> simp_all⟩, l.property⟩

/-- Diameter three and short-geodesic uniqueness supply the actual plane,
with the original coset incidence and both original actions. -/
@[instance_reducible] def projectivePlaneOfGeometry (q : ℕ) (hq : 1 < q)
    (hv : ∀ v, Nat.card ((graph F).neighborSet v) = q + 1) :
    ProjectivePlane (Point F) (Line F) := by
  classical
  let : Fintype (Point F) := Fintype.ofFinite _
  let : Fintype (Line F) := Fintype.ofFinite _
  have hP := card_fiber_of_plane_geometry F hg hu hd q hv false
  have hL := card_fiber_of_plane_geometry F hg hu hd q hv true
  have hp (l : Line F) : pointCount (Point F) l = q + 1 :=
    (Nat.card_congr (pointsOnLineEquivNeighbors F l)).trans (hv l.val)
  have hl (p : Point F) : lineCount (Line F) p = q + 1 :=
    (Nat.card_congr (linesOnPointEquivNeighbors F p)).trans (hv p.val)
  have hi (l m : Line F) (hne : l ≠ m) : ∃ p : Point F, p ∈ l ∧ p ∈ m := by
    obtain ⟨p, hp, _⟩ := existsUnique_commonNeighbor_of_plane_geometry F hg hu hd
      (l.property.trans m.property.symm) (fun h => hne (Subtype.ext h))
    have ht : p.type = false := by
      have h := hp.1.1
      rw [l.property] at h
      cases ht : p.type <;> simp_all
    exact ⟨⟨p, ht⟩, hp.1.symm, hp.2.symm⟩
  letI : Nondegenerate (Point F) (Line F) :=
    nondegenerate_of_regular_counts q hq hP hL hp hl hi
  letI : HasPoints (Point F) (Line F) :=
    { ‹Nondegenerate (Point F) (Line F)› with
      mkPoint := fun {l m} h => (hi l m h).choose
      mkPoint_ax := fun {l m} h => (hi l m h).choose_spec }
  letI : HasLines (Point F) (Line F) := HasPoints.hasLines (by
    simpa only [Nat.card_eq_fintype_card] using hP.trans hL.symm)
  exact { ‹HasPoints (Point F) (Line F)›, ‹HasLines (Point F) (Line F)› with
    exists_config := exists_config_of_regular_counts q hq hP hp hl }
end
end Subgroup.CosetGeometry.RankTwo
