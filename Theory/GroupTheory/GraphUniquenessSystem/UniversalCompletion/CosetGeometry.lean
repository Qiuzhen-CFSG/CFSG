module

public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.Presentation
public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.CycleCovering
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The coset graph of the rank-three presentation

Vertices are left cosets of the embedded vertex group. An edge is a translate
of the pair represented by `1` and a local edge reversal. The canonical map of
the presentation induces a graph map to the original graph. Equality in a fiber
of this graph map detects the kernel of the canonical group homomorphism.

Local bijectivity and closure of translated local cycles are the geometric
inputs to the cycle-covering argument. The lemmas here fix the concrete graph
and its projection, without adding relations to the presentation.

Source: Aschbacher, *Sporadic Groups* (1994), §§35–37, especially 37.5.
-/

@[expose] public section
namespace Theory.GroupTheory.GraphUniquenessSystem.System.PathPresentation

universe u v
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable (U : System G V)

/-- Vertices of the coset graph of the presentation. -/
abbrev Coset := U.PathPresentation ⧸ (vertex U).range

/-- The vertex represented by a presentation element. -/
def coset (p : U.PathPresentation) : Coset U := QuotientGroup.mk p

/-- The canonical projection of coset vertices to the original vertex set. -/
def project : Coset U → V :=
  Quotient.lift (fun p => canonical U p • U.x) (by
    intro p q hpq
    obtain ⟨a, ha⟩ := QuotientGroup.leftRel_apply.mp hpq
    calc
      canonical U p • U.x = canonical U p • (canonical U (p⁻¹ * q) • U.x) := by
        rw [← ha, canonical_vertex]
        exact congrArg (fun z => canonical U p • z) a.property.symm
      _ = canonical U q • U.x := by simp [map_mul, map_inv, mul_smul])

@[simp] theorem project_coset (p : U.PathPresentation) :
    project U (coset U p) = canonical U p • U.x := rfl

@[simp] theorem project_one : project U (coset U 1) = U.x := by simp

/-- Equality of representatives is precisely membership of their difference in
 the embedded vertex group. -/
theorem coset_eq_iff (p q : U.PathPresentation) :
    coset U p = coset U q ↔ p⁻¹ * q ∈ (vertex U).range := QuotientGroup.eq

/-- Right multiplication by a vertex-group element does not change the coset. -/
@[simp] theorem coset_mul_vertex (p : U.PathPresentation) (a : U.vertexGroup) :
    coset U (p * vertex U a) = coset U p :=
  QuotientGroup.mk_mul_of_mem p ⟨a, rfl⟩

/-- The projection is equivariant for the canonical homomorphism. -/
theorem project_smul (p : U.PathPresentation) (a : Coset U) :
    project U (p • a) = canonical U p • project U a := by
  induction a using QuotientGroup.induction_on with
  | H q =>
    exact (congrArg (fun z => z • U.x) (map_mul (canonical U) p q)).trans
      (mul_smul _ _ _)

/-- All ambient vertices are in the image of the coset projection. -/
theorem project_surjective : Function.Surjective (project U) := by
  intro a
  obtain ⟨g, hg⟩ := U.vertex_transitive a
  obtain ⟨p, hp⟩ := canonical_surjective U g
  exact ⟨coset U p, by simpa only [project_coset, hp] using hg⟩

/-- Local orbit vertices have exactly the expected equalities in the coset graph. -/
theorem coset_local_eq_iff (h k : U.H) :
    coset U (localMap U h) = coset U (localMap U k) ↔
      (h : G) • U.x = (k : G) • U.x := by
  constructor
  · intro he
    simpa only [project_coset, canonical_local] using congrArg (project U) he
  · intro he
    apply (coset_eq_iff U _ _).mpr
    have hv : ((h⁻¹ * k : U.H) : G) ∈ U.vertexGroup := by
      change ((h : G)⁻¹ * (k : G)) • U.x = U.x
      rw [mul_smul, ← he, inv_smul_smul]
    refine ⟨⟨h⁻¹ * k, hv⟩, ?_⟩
    have hc := (inclusions U).local_vertex _ (h⁻¹ * k).property hv
    change localMap U (h⁻¹ * k) = vertex U ⟨h⁻¹ * k, hv⟩ at hc
    rw [← hc, map_mul, map_inv]

variable (t : U.H)

/-- Edges are the translates of the distinguished pair, in either orientation. -/
def CosetAdj (a b : Coset U) : Prop :=
  ∃ p : U.PathPresentation,
    (coset U p = a ∧ coset U (p * localMap U t) = b) ∨
    (coset U p = b ∧ coset U (p * localMap U t) = a)

/-- Every coset edge projects to an actual ambient edge. -/
theorem project_adj (htx : (t : G) • U.x = U.y) {a b : Coset U}
    (h : CosetAdj U t a b) : U.graph.Adj (project U a) (project U b) := by
  obtain ⟨p, h | h⟩ := h
  · rcases h with ⟨rfl, rfl⟩
    simpa only [project_coset, map_mul, canonical_local, mul_smul, htx] using
      U.preserves (canonical U p) U.adjacent
  · rcases h with ⟨rfl, rfl⟩
    simpa only [project_coset, map_mul, canonical_local, mul_smul, htx] using
      (U.preserves (canonical U p) U.adjacent).symm

/-- The graph attached to a local edge reversal in the rank-three presentation. -/
def cosetGraph (htx : (t : G) • U.x = U.y) : SimpleGraph (Coset U) where
  Adj := CosetAdj U t
  symm := ⟨by
    rintro a b ⟨p, h | h⟩
    · exact ⟨p, Or.inr h⟩
    · exact ⟨p, Or.inl h⟩⟩
  loopless := ⟨fun a h => (project_adj U t htx h).ne rfl⟩

/-- The concrete graph homomorphism used in the covering proof. -/
def projection (htx : (t : G) • U.x = U.y) : cosetGraph U t htx →g U.graph where
  toFun := project U
  map_rel' := project_adj U t htx

@[simp] theorem projection_apply (htx : (t : G) • U.x = U.y) (a : Coset U) :
    projection U t htx a = project U a := rfl

/-- Each translate of the distinguished pair is an edge. -/
theorem cosetGraph_adj (htx : (t : G) • U.x = U.y) (p : U.PathPresentation) :
    (cosetGraph U t htx).Adj (coset U p) (coset U (p * localMap U t)) :=
  ⟨p, Or.inl ⟨rfl, rfl⟩⟩

/-- Left translation preserves the coset graph. -/
theorem cosetGraph_smul (htx : (t : G) • U.x = U.y) (p : U.PathPresentation)
    {a b : Coset U} (h : (cosetGraph U t htx).Adj a b) :
    (cosetGraph U t htx).Adj (p • a) (p • b) := by
  obtain ⟨q, h | h⟩ := h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨p * q, Or.inl ⟨rfl, by
      change coset U ((p * q) * localMap U t) = coset U (p * (q * localMap U t))
      rw [mul_assoc]⟩⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨p * q, Or.inr ⟨rfl, by
      change coset U ((p * q) * localMap U t) = coset U (p * (q * localMap U t))
      rw [mul_assoc]⟩⟩

/-- Injectivity of the coset projection detects the full group kernel. -/
theorem canonical_injective_of_project_injective (hi : Function.Injective (project U)) :
    Function.Injective (canonical U) := by
  apply (injective_iff_map_eq_one (canonical U)).mpr
  intro p hp
  have hq : coset U 1 = coset U p := hi (by simp [hp])
  have hm : p ∈ (vertex U).range := by simpa using (coset_eq_iff U 1 p).mp hq
  obtain ⟨a, rfl⟩ := hm
  have ha : a = 1 := Subtype.ext (by simpa only [canonical_vertex, Subgroup.coe_one] using hp)
  rw [ha, map_one]

/-- The cycle-covering theorem reduces global injectivity to the two concrete
 geometric properties of the coset projection and connectedness of its source. -/
theorem canonical_bijective_of_cover (htx : (t : G) • U.x = U.y)
    (hb : U.IsBase)
    (hc : (cosetGraph U t htx).Preconnected)
    (hf : ∀ a, Function.Bijective ((projection U t htx).mapNeighborSet a))
    (hs : ∀ a (p : U.graph.Walk a a), p ∈ U.baseCycles a →
      ((projection U t htx).coverTransport hf).along p = Equiv.refl _) :
    Function.Bijective (canonical U) :=
  ⟨canonical_injective_of_project_injective U
      ((projection U t htx).injective_of_cycleBase hf hc hb hs), canonical_surjective U⟩

end Theory.GroupTheory.GraphUniquenessSystem.System.PathPresentation
