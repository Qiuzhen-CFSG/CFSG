module

public import ABG.Recognition.ThreeLinearMSubgroup
public import ABG.Recognition.ThreeLinearIndex39
public import ABG.Recognition.ThreeLinearPermutationCharacter

/-!
# Wong's subgroup of index thirteen

For the linear branch of order 5616, construct the actual subgroup
`K = M ⊔ C_G(τ)` and its faithful doubly transitive action on thirteen cosets.
The permutation character and all fixed-point counts use the same catalog
as the construction of `M`.

The order-36 subgroup and the centralizer have a proper join by their fixed
space dimensions. The index alternatives and the exclusion of index 39 give
index 13; the permutation-character theorem supplies the action properties.
The first assembly theorem preserves a supplied local catalog, and the second
constructs that catalog from the original recognition hypotheses.

This module also re-exports `ThreeLinearPermutationData` and its reusable
`fixedPoint_count`, `fixedPoint_counts`, `fixedPoint_count_pointElement`,
`fixedPoint_count_other_order_three`, and `fixedPoint_count_involution`
identities on the constructed cosets.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), Theorem 6(b), printed pp.110–111.
-/

namespace ABG
noncomputable section
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Construct Wong's actual index-thirteen subgroup and its coset action,
retaining the prescribed local character catalog. -/
public theorem ThreeLinearLocalData.exists_indexThirteen_subgroup
    (c : ThreeLinearLocalData G)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    ∃ M K : Subgroup G,
      c.MSubgroupConfiguration M ∧
      K = M ⊔ Subgroup.centralizer ({c.involution} : Set G) ∧
      K.index = 13 ∧
      FaithfulSMul G (G ⧸ K) ∧
      MulAction.IsMultiplyPretransitive G (G ⧸ K) 2 ∧
      (ThreeGlobalDegreeData.cosetRepresentation K).character = 1 + c.decomposition.χ 5 ∧
      ∀ g : G, (Nat.card (MulAction.fixedBy (G ⧸ K) g) : ℂ) =
        1 + c.decomposition.χ 5 g := by
  obtain ⟨d, rfl⟩ := c.exists_permutationData hC
  exact ⟨d.M, d.subgroup, d.configuration, rfl, d.subgroup_index,
    d.faithful, d.two_pretransitive, d.permutation_character, d.fixedPoint_count⟩

/-- The original simple-group, semidihedral Sylow-two, and GL₂(3) centralizer
hypotheses in the order-5616 branch yield Wong's subgroup and character identity. -/
public theorem exists_threeLinearIndexThirteen
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (hG : Nat.card G = 5616) :
    ∃ c : ThreeLinearLocalData G, ∃ M K : Subgroup G,
      c.MSubgroupConfiguration M ∧
      K = M ⊔ Subgroup.centralizer ({c.involution} : Set G) ∧
      K.index = 13 ∧
      FaithfulSMul G (G ⧸ K) ∧
      MulAction.IsMultiplyPretransitive G (G ⧸ K) 2 ∧
      (ThreeGlobalDegreeData.cosetRepresentation K).character = 1 + c.decomposition.χ 5 ∧
      ∀ g : G, (Nat.card (MulAction.fixedBy (G ⧸ K) g) : ℂ) =
        1 + c.decomposition.χ 5 g := by
  obtain ⟨c⟩ := exists_threeLinearLocalData S hS hcard hC hG
  exact ⟨c, c.exists_indexThirteen_subgroup hC⟩

end
end ABG
