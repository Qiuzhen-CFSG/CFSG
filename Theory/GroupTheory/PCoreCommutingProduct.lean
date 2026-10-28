module
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Prime cores of commuting disjoint subgroups

Multiplication identifies the joined subgroup with the external direct product.
Transporting its prime core through this actual equivalence identifies the
embedded core with the join of the embedded cores of the two factors.
-/

public section
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem pCoreIn_sup_of_disjoint_of_commuting (p : ℕ) [Fact p.Prime]
    (A B : Subgroup G) (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G)) :
    (A ⊔ B).pCoreIn p = A.pCoreIn p ⊔ B.pCoreIn p := by
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  change (pCore p (A ⊔ B : Subgroup G)).map (A ⊔ B).subtype = _
  rw [← pCore_map_iso p e, pCore_prod, map_map]
  apply le_antisymm
  · rintro g ⟨⟨a,b⟩,hab,rfl⟩
    change (e (a,b) : G) ∈ _
    rw [he]
    exact mul_mem_sup (mem_map_of_mem A.subtype hab.1) (mem_map_of_mem B.subtype hab.2)
  · apply sup_le
    · rintro g ⟨a,ha,rfl⟩
      refine ⟨(a,1),⟨ha,one_mem _⟩,?_⟩
      change (e (a,1) : G) = _
      rw [he]
      exact mul_one _
    · rintro g ⟨b,hb,rfl⟩
      refine ⟨(1,b),⟨one_mem _,hb⟩,?_⟩
      change (e (1,b) : G) = _
      rw [he]
      exact one_mul _
end Subgroup
