module
public import Theory.SpecificGroups.OmegaSixThree.UnitaryFlagCore
public import Theory.SpecificGroups.OmegaSixThree.EdgeCardinality
public import Theory.GroupTheory.PResidual.Quotient
/-!
# The local edge fixer supplements the edge two-residual

In the literal S4×S4 coordinates the pointwise edge fixer is V4×S4, of
order96. Its index in the edge group of order1440 is15. The index of a
subgroup containing the two-residual divides a power of two; it cannot also
divide15 unless it is one. Thus the local edge fixer and the two-residual
generate the edge, exactly as required for the F.5.7 conjugation identity.

Source: Aschbacher--Smith F.5.7(3), printed p.303.
-/

open Subgroup
namespace OmegaSixThree.TriangleLocal
open OrthogonalityGraph VertexComparison.FlagWords
open Theory.SpecificGroups.SymmetricSix.DuadCalculation (core)
public noncomputable section
local notation "E" => modelSystem.edgeGroup

theorem edge_subgroupOf_local : (E).subgroupOf H=fixedPlaneLocal := by
  ext g
  have hv : g∈vertexLocal ↔ (productEquiv g).1∈square := by
    rw [vertexLocal_eq]
    change ((productEquiv g).1∈square ∧ (productEquiv g).2∈(⊤ : Subgroup Four)) ↔ _
    simp
  have hc : g*graphElement=graphElement*g ↔
      (productEquiv g).1*(Equiv.swap 0 3*Equiv.swap 1 2)=
        (Equiv.swap 0 3*Equiv.swap 1 2)*(productEquiv g).1 := by
    constructor
    · intro h
      have he := congrArg productEquiv h
      rw [map_mul,map_mul,graphElement_image] at he
      exact congrArg Prod.fst he
    · intro h
      apply productEquiv.injective
      rw [map_mul,map_mul,graphElement_image]
      exact Prod.ext h (by simp)
  have he : g∈(E).subgroupOf H ↔ g∈vertexLocal ∧ g*graphElement=graphElement*g := by
    change g.val∈Theory.GroupTheory.GraphUniquenessSystem.edgeFixer
      omegaPlusSixThree standardFirst standardSecond ↔ _
    rw [edgeFixer_eq_vertex_inf_graph_centralizer]
    change (g∈vertexLocal ∧ g.val∈centralizer ({vertexGraphInvolution}:Set omegaPlusSixThree)) ↔ _
    rw [mem_centralizer_singleton_iff]
    exact and_congr_right (fun _ => ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩)
  rw [he,hv,hc]
  change _ ↔ ((productEquiv g).1∈core ∧ (productEquiv g).2∈(⊤ : Subgroup Four))
  simp only [mem_top,and_true]
  exact (show ∀p:Four,(p∈square ∧ p*(Equiv.swap 0 3*Equiv.swap 1 2)=
    (Equiv.swap 0 3*Equiv.swap 1 2)*p) ↔ p∈core by decide +kernel) _

def localEdgeEquiv : H.subgroupOf E ≃* (E).subgroupOf H where
  toFun g := ⟨⟨g.val.val,g.property⟩,g.val.property⟩
  invFun g := ⟨⟨g.val.val,g.property⟩,g.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem card_localEdge : Nat.card (H.subgroupOf E)=96 := by
  rw [Nat.card_congr localEdgeEquiv.toEquiv,edge_subgroupOf_local]
  exact fixedPlaneLocal_card

def edgeVertexStabilizerEquiv : E ≃*
    MulAction.stabilizer (MulAction.stabilizer omegaPlusSixThree standardFirst) standardSecond where
  toFun g := ⟨⟨g.val,g.property.1⟩,g.property.2⟩
  invFun g := ⟨g.val.val,g.val.property,g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem card_edge : Nat.card E=1440 :=
  (Nat.card_congr edgeVertexStabilizerEquiv.toEquiv).trans card_vertex_second_stabilizer

theorem localEdge_index : (H.subgroupOf E).index=15 := by
  have hh := (H.subgroupOf E).card_mul_index
  rw [card_edge,card_localEdge] at hh
  omega

/-- The actual local edge fixer supplements the edge two-residual. -/
theorem edge_twoResidual_sup_local : pResidual 2 E ⊔ H.subgroupOf E=⊤ := by
  let : Finite E := Nat.finite_of_card_ne_zero (by rw [card_edge]; decide)
  obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G:=E) 2).exists_card_eq
  have hr : (pResidual 2 E).index=2^n := by rw [index_eq_card,hn]
  apply index_eq_one.mp
  apply Nat.eq_one_of_dvd_coprimes
    (show Nat.Coprime (pResidual 2 E).index (H.subgroupOf E).index from by
      rw [hr,localEdge_index]
      exact (show Nat.Coprime 2 15 by decide).pow_left n)
    (index_dvd_of_le le_sup_left) (index_dvd_of_le le_sup_right)
end
end OmegaSixThree.TriangleLocal
