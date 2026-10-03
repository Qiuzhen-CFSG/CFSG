module

public import FeitThompson.BGsection1.proposition_1_16

public import Theory.GroupTheory.FocalTransfer

public section

/-
**Kind**: Theorem
**Note**: Theorem 1.17
**Stmt**:
Let `G` be a finite group.
Let `p` be a prime.
Let `S` be a Sylow `p`-subgroup of `G`.
Then
`S ∩ G' = ⟨ x⁻¹ y | x, y ∈ S and x is conjugate to y in G ⟩`.
-/

public theorem theorem_1_17 {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (S : Sylow p G) :
    ((S : Subgroup G) ⊓ derivedSubgroup G) =
      Subgroup.closure {z : G | ∃ x : G, x ∈ (S : Subgroup G) ∧ ∃ y : G, y ∈ (S : Subgroup G) ∧
        IsConj x y ∧ z = x⁻¹ * y} := by
  simpa using sylow_inf_derivedSubgroup_eq_focalSubgroup (G := G) p S


end
