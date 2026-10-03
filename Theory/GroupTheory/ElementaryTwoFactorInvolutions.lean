module
public import Theory.GroupTheory.TwoElementaryIndexTwo

/-!
# Involutions in a product of two elementary factors

Let `C` and `D` be elementary abelian two-subgroups of a finite group, each
normalizing the other. Suppose their intersection has index two in each
factor and their join is noncommutative. Every element of the join whose
square is one then belongs to one of the factors.

The proof restricts both factors to their join. Normalization and the relative
index formula show that each restricted factor has index two. They are
distinct, since their join is the whole group and their indices are two.
The existing elementary-subgroup classification for two index-two factors
then applies to the cyclic subgroup of the given element. Noncommutativity
supplies its non-elementarity hypothesis.

This source-neutral finite-group lemma is used in the small-quotient argument
of Stellmacher, Journal of Algebra 190 (1997), (9.1), p.46. Its index-two
classification prerequisite is developed in `TwoElementaryIndexTwo`.
-/

namespace Subgroup

private theorem relIndex_sup_of_normalizes
    {G : Type*} [Group G] (C D : Subgroup G)
    (hDC : D ≤ normalizer (C : Set G)) : C.relIndex (C ⊔ D) = C.relIndex D := by
  let J := C ⊔ D
  let _ : (C.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hDC)
  have h := relIndex_sup_left (D.subgroupOf J) (C.subgroupOf J)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf le_sup_right] at h
  exact h

/-- Every square-one element of a noncommutative normalized product of two
elementary factors with intersection of index two lies in a factor. -/
public theorem involution_mem_union_of_elementary_factors_index_two
    {G : Type*} [Group G] [Finite G]
    (C D : Subgroup G) (hC : IsElementaryAbelian 2 C)
    (hD : IsElementaryAbelian 2 D)
    (hCD : C ≤ normalizer (D : Set G)) (hDC : D ≤ normalizer (C : Set G))
    (hIC : (C ⊓ D).relIndex C = 2) (hID : (C ⊓ D).relIndex D = 2)
    (hcomm : ¬ IsMulCommutative ↥(C ⊔ D))
    {v : G} (hv : v ∈ C ⊔ D) (hv2 : v ^ 2 = 1) : v ∈ C ∨ v ∈ D := by
  let J := C ⊔ D
  let A := C.subgroupOf J
  let B := D.subgroupOf J
  let _ : IsElementaryAbelian 2 C := hC
  let _ : IsElementaryAbelian 2 D := hD
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf le_sup_left
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf le_sup_right
  have hAi : A.index = 2 := by
    change C.relIndex (C ⊔ D) = 2
    rw [relIndex_sup_of_normalizes C D hDC, ← inf_relIndex_right]
    exact hID
  have hBi : B.index = 2 := by
    change D.relIndex (C ⊔ D) = 2
    rw [sup_comm, relIndex_sup_of_normalizes D C hCD, ← inf_relIndex_left]
    exact hIC
  have hsup : A ⊔ B = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self _
  have hne : A ≠ B := by
    intro heq
    have hAtop : A = ⊤ := by simpa only [← heq, sup_idem] using hsup
    rw [hAtop, index_top] at hAi
    contradiction
  have hJ : ¬ IsElementaryAbelian 2 J := fun h => hcomm h.toIsMulCommutative
  let x : J := ⟨v, hv⟩
  have hx2 : x ^ 2 = 1 := Subtype.ext hv2
  have hE : IsElementaryAbelian 2 (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hx2
  obtain h | h := elementary_le_one_of_two_index_two A B hA hB hAi hBi hne hJ
    (zpowers x) hE
  · exact Or.inl (h (mem_zpowers x))
  · exact Or.inr (h (mem_zpowers x))

end Subgroup
