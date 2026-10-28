module

public import Theory.GroupAction.RankTwoCosetCover
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Restricting a rank-two coset graph to a normal subgroup

If a normal subgroup and the common vertex subgroup generate the ambient
group, inclusion induces an isomorphism from the restricted coset graph onto
the original graph. Every ambient element has a normal-subgroup representative
simultaneously in both coset spaces; this proves surjectivity and reflects
incidence. The isomorphism respects the action, types and right-coset convention.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (3.2),
printed pp.386--387, restriction to the two-perfect normal subgroup.
-/

@[expose] public section
open Subgroup
namespace Subgroup.CosetGeometry.RankTwo.NormalRestriction
variable {G : Type*} [Group G] (F : Bool → Subgroup G) (N : Subgroup G)

/-- The two literal intersections, regarded as subgroups of `N`. -/
abbrev family : Bool → Subgroup N := fun i => (F i).subgroupOf N

/-- The coset map induced by the subgroup inclusion. -/
def coset (i : Bool) : N ⧸ family F N i → G ⧸ F i :=
  Quotient.map N.subtype (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have hmem : (a⁻¹ * b : N) ∈ (F i).subgroupOf N :=
      QuotientGroup.leftRel_apply.mp hab
    exact hmem)

@[simp] theorem coset_mk (i : Bool) (n : N) :
    coset F N i (n : N ⧸ family F N i) = ((n : G) : G ⧸ F i) := rfl

theorem coset_injective (i : Bool) : Function.Injective (coset F N i) := by
  intro u v huv
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
  apply QuotientGroup.eq.mpr
  change ((a : G) : G ⧸ F i) = ((b : G) : G ⧸ F i) at huv
  have hmem : (a : G)⁻¹ * (b : G) ∈ F i := QuotientGroup.eq.mp huv
  exact hmem

/-- Inclusion of typed coset vertices. -/
def vertex (v : Vertex (family F N)) : Vertex F := ⟨v.type, coset F N v.type v.coset⟩

@[simp] theorem vertex_mk (i : Bool) (n : N) :
    vertex F N (mkVertex (family F N) i n) = mkVertex F i n := rfl

@[simp] theorem vertex_type (v : Vertex (family F N)) :
    (vertex F N v).type = v.type := rfl

@[simp] theorem vertex_base (i : Bool) :
    vertex F N (base (family F N) i) = base F i := rfl

@[simp] theorem vertex_smul (n : N) (v : Vertex (family F N)) :
    vertex F N (n • v) = (n : G) • vertex F N v := by
  rcases v with ⟨i, q⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

@[simp] theorem vertex_rightVertex (i : Bool) (n : N) :
    vertex F N (rightVertex (family F N) i n) = rightVertex F i n := by
  simp only [rightVertex, vertex_smul, vertex_base, Subgroup.coe_inv]

theorem vertex_injective : Function.Injective (vertex F N) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ huv
  have hij := congrArg (fun v : Vertex F => v.type) huv
  change i = j at hij
  subst j
  have he : coset F N i u = coset F N i v := by
    simpa only [vertex, CosetGeometry.Vertex.mk.injEq, heq_eq_eq, true_and] using huv
  exact congrArg (CosetGeometry.Vertex.mk i) (coset_injective F N i he)

variable [N.Normal]

/-- A common representative in `N` for both ambient left cosets. -/
theorem exists_normal_representative (hs : N ⊔ (F false ⊓ F true) = ⊤) (g : G) :
    ∃ n : N, ∀ i, ((n : G) : G ⧸ F i) = (g : G ⧸ F i) := by
  have hg : g ∈ N ⊔ (F false ⊓ F true) := hs.symm ▸ mem_top g
  obtain ⟨n, hn, b, hb, hnb⟩ := mem_sup_of_normal_left.mp hg
  refine ⟨⟨n, hn⟩, fun i => ?_⟩
  apply QuotientGroup.eq.mpr
  rw [← hnb, inv_mul_cancel_left]
  cases i
  · exact hb.1
  · exact hb.2

theorem vertex_surjective (hs : N ⊔ (F false ⊓ F true) = ⊤) :
    Function.Surjective (vertex F N) := by
  rintro ⟨i, q⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨n, hn⟩ := exists_normal_representative F N hs g
  exact ⟨mkVertex (family F N) i n, congrArg (CosetGeometry.Vertex.mk i) (hn i)⟩

theorem incident_iff (hs : N ⊔ (F false ⊓ F true) = ⊤) (v w : Vertex (family F N)) :
    Incident F (vertex F N v) (vertex F N w) ↔ Incident (family F N) v w := by
  constructor
  · rintro ⟨g, hv, hw⟩
    obtain ⟨n, hn⟩ := exists_normal_representative F N hs g
    refine ⟨n, coset_injective F N v.type ?_, coset_injective F N w.type ?_⟩
    · exact (hn v.type).trans hv
    · exact (hn w.type).trans hw
  · rintro ⟨n, hv, hw⟩
    exact ⟨n, congrArg (coset F N v.type) hv, congrArg (coset F N w.type) hw⟩

/-- The original graph is unchanged on restriction to a normal subgroup
supplemented by the common vertex subgroup. -/
noncomputable def graphIso (hs : N ⊔ (F false ⊓ F true) = ⊤) :
    graph (family F N) ≃g graph F where
  toEquiv := Equiv.ofBijective (vertex F N) ⟨vertex_injective F N, vertex_surjective F N hs⟩
  map_rel_iff' := by
    intro v w
    exact and_congr Iff.rfl (incident_iff F N hs v w)

@[simp] theorem graphIso_apply (hs : N ⊔ (F false ⊓ F true) = ⊤)
    (v : Vertex (family F N)) : graphIso F N hs v = vertex F N v := rfl

theorem isTree_iff (hs : N ⊔ (F false ⊓ F true) = ⊤) :
    (graph (family F N)).IsTree ↔ (graph F).IsTree :=
  (graphIso F N hs).isTree_iff

end Subgroup.CosetGeometry.RankTwo.NormalRestriction
