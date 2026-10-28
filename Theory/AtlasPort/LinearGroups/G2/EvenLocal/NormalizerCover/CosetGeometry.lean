module

public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.HexagonData

/-!+# The incidence action of the actual G₂ parabolics

Vertices are left cosets of the two root-defined subgroups of the octonion
automorphism group. An edge is a pair of cosets with a common representative.
Thus the vertex stabilizers are actual conjugates of the displayed parabolics.
This module does not yet assert the generalized-hexagon axioms.

Sylow conjugacy gives a fixed edge for every two-subgroup, including subgroups
which are not characteristic in any Sylow subgroup. A vertex fixed by its
normalizer yields the precise conjugate containment used in the quasithin
converse. Source: the rank-two Borel--Tits argument for Aschbacher--Smith,
Theorem 0.1.2(1), printed pp.3--4 and pp.481--482.
-/

@[expose] public section

namespace Atlas.G2.EvenLocal.NormalizerCover

open LieParabolicSetup
open scoped Pointwise

variable (F : Type*) [Field F]

/-- Two types of cosets of the root-defined parabolics in the octonion model. -/
abbrev Vertex := (Model F ⧸ parabolic₁) ⊕ (Model F ⧸ parabolic₂)

instance [Finite F] : Finite (Vertex F) := by
  unfold Vertex
  infer_instance

instance : MulAction (Model F) (Vertex F) where
  smul g v := match v with
    | Sum.inl x => Sum.inl (g • x)
    | Sum.inr y => Sum.inr (g • y)
  one_smul v := by
    cases v with
    | inl x => exact congrArg Sum.inl (one_smul (Model F) x)
    | inr y => exact congrArg Sum.inr (one_smul (Model F) y)
  mul_smul g h v := by
    cases v with
    | inl x => exact congrArg Sum.inl (mul_smul g h x)
    | inr y => exact congrArg Sum.inr (mul_smul g h y)

variable {F}

/-- The short-side vertex represented by an element of the actual group. -/
def shortVertex (g : Model F) : Vertex F := Sum.inl (g : Model F ⧸ parabolic₁)

/-- The long-side vertex represented by an element of the actual group. -/
def longVertex (g : Model F) : Vertex F := Sum.inr (g : Model F ⧸ parabolic₂)

@[simp] theorem smul_shortVertex (g h : Model F) :
    g • shortVertex h = shortVertex (g * h) := rfl

@[simp] theorem smul_longVertex (g h : Model F) :
    g • longVertex h = longVertex (g * h) := rfl

/-- The group action preserves the two types of vertices. -/
def vertexColor : Vertex F → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

@[simp] theorem vertexColor_smul (g : Model F) (v : Vertex F) :
    vertexColor (g • v) = vertexColor v := by cases v <;> rfl

theorem vertex_cases (v : Vertex F) :
    (∃ g : Model F, v = shortVertex g) ∨ ∃ g : Model F, v = longVertex g := by
  cases v with
  | inl x =>
    refine Or.inl ?_
    induction x using Quotient.inductionOn' with
    | h g => exact ⟨g, rfl⟩
  | inr y =>
    refine Or.inr ?_
    induction y using Quotient.inductionOn' with
    | h g => exact ⟨g, rfl⟩

/-- Incidence means that the two left cosets have a common representative. -/
def incidenceGraph : SimpleGraph (Vertex F) where
  Adj x y :=
    (∃ g : Model F, x = shortVertex g ∧ y = longVertex g) ∨
    (∃ g : Model F, x = longVertex g ∧ y = shortVertex g)
  symm := by
    constructor
    rintro x y (⟨g, hx, hy⟩ | ⟨g, hx, hy⟩)
    · exact Or.inr ⟨g, hy, hx⟩
    · exact Or.inl ⟨g, hy, hx⟩
  loopless := by
    constructor
    rintro x (⟨g, rfl, h⟩ | ⟨g, rfl, h⟩) <;> cases h

theorem incident_vertices_different_colors {x y : Vertex F}
    (h : incidenceGraph.Adj x y) : vertexColor x ≠ vertexColor y := by
  rcases h with ⟨g, rfl, rfl⟩ | ⟨g, rfl, rfl⟩ <;>
    simp [vertexColor, shortVertex, longVertex]

theorem smul_incident (g : Model F) {x y : Vertex F}
    (h : incidenceGraph.Adj x y) : incidenceGraph.Adj (g • x) (g • y) := by
  rcases h with ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · exact Or.inl ⟨g * k, rfl, rfl⟩
  · exact Or.inr ⟨g * k, rfl, rfl⟩

theorem mem_stabilizer_shortVertex (g h : Model F) :
    h ∈ MulAction.stabilizer (Model F) (shortVertex g) ↔
      g⁻¹ * h * g ∈ parabolic₁ := by
  rw [MulAction.mem_stabilizer_iff, smul_shortVertex]
  change Sum.inl (↑(h * g) : Model F ⧸ parabolic₁) =
    (Sum.inl (↑g : Model F ⧸ parabolic₁) : Vertex F) ↔ _
  rw [Sum.inl.injEq, eq_comm, QuotientGroup.eq, ← mul_assoc]

theorem mem_stabilizer_longVertex (g h : Model F) :
    h ∈ MulAction.stabilizer (Model F) (longVertex g) ↔
      g⁻¹ * h * g ∈ parabolic₂ := by
  rw [MulAction.mem_stabilizer_iff, smul_longVertex]
  change Sum.inr (↑(h * g) : Model F ⧸ parabolic₂) =
    (Sum.inr (↑g : Model F ⧸ parabolic₂) : Vertex F) ↔ _
  rw [Sum.inr.injEq, eq_comm, QuotientGroup.eq, ← mul_assoc]

@[simp] theorem stabilizer_shortVertex_one :
    MulAction.stabilizer (Model F) (shortVertex (1 : Model F)) = parabolic₁ := by
  apply Subgroup.ext
  intro h
  rw [mem_stabilizer_shortVertex]
  simp

@[simp] theorem stabilizer_longVertex_one :
    MulAction.stabilizer (Model F) (longVertex (1 : Model F)) = parabolic₂ := by
  apply Subgroup.ext
  intro h
  rw [mem_stabilizer_longVertex]
  simp

/-- Every two-subgroup fixes an incident pair in the concrete coset geometry. -/
theorem exists_fixed_edge [Finite F] [CharP F 2]
    (R : Subgroup (Model F)) (hp : IsPGroup 2 R) :
    ∃ x y : Vertex F, incidenceGraph.Adj x y ∧
      x ∈ fixedVertices R ∧ y ∈ fixedVertices R := by
  obtain ⟨S, hRS⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F) S (sylow (F := F))
  have hconj : ∀ r ∈ R, g * r * g⁻¹ ∈ unipotent := by
    intro r hr
    have hm : (MulAut.conj g) r ∈
        (MulAut.conj g) • (S : Subgroup (Model F)) :=
      Subgroup.mem_map.mpr ⟨r, hRS hr, rfl⟩
    change g * r * g⁻¹ ∈ (g • S : Sylow 2 (Model F)) at hm
    rw [hg] at hm
    exact hm
  refine ⟨shortVertex g⁻¹, longVertex g⁻¹, Or.inl ⟨g⁻¹, rfl, rfl⟩, ?_, ?_⟩
  · intro r hr
    apply MulAction.mem_stabilizer_iff.mp
    apply (mem_stabilizer_shortVertex _ _).mpr
    simpa only [inv_inv] using
      borel_le_parabolic₁ (Subgroup.mem_sup_left (hconj r hr))
  · intro r hr
    apply MulAction.mem_stabilizer_iff.mp
    apply (mem_stabilizer_longVertex _ _).mpr
    simpa only [inv_inv] using
      borel_le_parabolic₂ (Subgroup.mem_sup_left (hconj r hr))

/-- Converting a geometric fixed vertex to the required subgroup map uses
the inverse of its left-coset representative as conjugator. -/
theorem normalizer_conjugate_le_of_fixed_vertex (R : Subgroup (Model F))
    (v : Vertex F)
    (hv : ∀ n ∈ Subgroup.normalizer (R : Set (Model F)), n • v = v) :
    ∃ g : Model F,
      (Subgroup.normalizer (R : Set (Model F))).map (MulAut.conj g).toMonoidHom ≤
        parabolic₁ ∨
      (Subgroup.normalizer (R : Set (Model F))).map (MulAut.conj g).toMonoidHom ≤
        parabolic₂ := by
  rcases vertex_cases v with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · refine ⟨g⁻¹, Or.inl ?_⟩
    rintro k ⟨n, hn, rfl⟩
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv] using
      (mem_stabilizer_shortVertex g n).mp (hv n hn)
  · refine ⟨g⁻¹, Or.inr ?_⟩
    rintro k ⟨n, hn, rfl⟩
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv] using
      (mem_stabilizer_longVertex g n).mp (hv n hn)

/-- Long-type cosets are exactly the singular projective points of the split
octonion algebra, with their existing automorphism action. -/
noncomputable def longCosetEquivSingularPoints :
    (Model F ⧸ parabolic₂) ≃ SingularPoints F :=
  (Subgroup.quotientEquivOfEq parabolic_eq_pointStabilizer).trans
    (Equiv.ofBijective (MulAction.ofQuotientStabilizer (Model F) firstPoint)
      ⟨MulAction.injective_ofQuotientStabilizer (Model F) firstPoint, by
        intro p
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F) firstPoint p
        exact ⟨(g : Model F ⧸ pointStabilizer), hg⟩⟩)

@[simp] theorem longCosetEquivSingularPoints_coe (g : Model F) :
    longCosetEquivSingularPoints (g : Model F ⧸ parabolic₂) =
      g • firstPoint := rfl

/-- The coset-to-octonion identification is equivariant, not just a bijection
between sets of the same cardinality. -/
theorem longCosetEquivSingularPoints_smul (g : Model F)
    (v : Model F ⧸ parabolic₂) :
    longCosetEquivSingularPoints (g • v) = g • longCosetEquivSingularPoints v := by
  induction v using Quotient.inductionOn' with
  | h k => exact mul_smul g k (firstPoint (K := F))

end Atlas.G2.EvenLocal.NormalizerCover
