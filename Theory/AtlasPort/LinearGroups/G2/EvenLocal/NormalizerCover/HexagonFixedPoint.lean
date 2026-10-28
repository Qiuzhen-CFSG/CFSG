module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.HexagonFixedPoint.FixedTree
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.HexagonFixedPoint.TreeCenter

/-!
# A normalizer fixed point from the fixed hexagon tree

The fixed vertices of a nonidentity two-subgroup with a fixed incident pair
induce a finite tree. Its normalizer acts on this tree by automorphisms. The
finite-tree center is invariant, and preserved vertex colors prevent swapping
the endpoints when the center is an edge, giving a normalizer fixed vertex.

This is a conditional geometric helper for the defining-characteristic rank-two
Borel--Tits step in Aschbacher--Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed pp. 3--4 and 481--482. Applications supply the actual
G₂ hexagon and its fixed incident pair; all graph and center deductions from
those hypotheses are proved here.
-/

@[expose] public section

namespace Atlas.G2.EvenLocal.NormalizerCover

variable {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
variable {Γ : SimpleGraph X} {color : X → Bool}

/-- In a finite hexagon action, the normalizer of a nonidentity two-subgroup
fixing an incident pair fixes a vertex. The normalizer need not be a two-group. -/
theorem normalizer_fixed_vertex_of_fixed_edge
    (hΓ : HexagonData (G := G) Γ color) (R : Subgroup G)
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

end Atlas.G2.EvenLocal.NormalizerCover
