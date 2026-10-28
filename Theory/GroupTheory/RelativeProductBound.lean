module
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Pointwise.Set.Card

/-!
# Relative order of a subgroup contained in a set product

Passing to the quotient by a normal subgroup sends a set product to the
product of its images. The cardinality of this product is at most the
product of their cardinalities, giving the corresponding relative-index
bound without assuming that the factors contain the kernel.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] (N H A B : Subgroup G) [N.Normal]
  [Finite A] [Finite B]
/-- A set product bounds relative order after the literal quotient map. -/
theorem relIndex_le_mul_of_subset_product
    (h : (H : Set G) ⊆ (A : Set G) * (B : Set G)) :
    N.relIndex H ≤ N.relIndex A * N.relIndex B := by
  let q := QuotientGroup.mk' N
  have hm : (H.map q : Set (G ⧸ N)) ⊆ (A.map q : Set (G ⧸ N)) * (B.map q : Set (G ⧸ N)) := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨a,ha,b,hb,rfl⟩ := h hy
    exact ⟨q a,mem_map_of_mem q ha,q b,mem_map_of_mem q hb,(q.map_mul a b).symm⟩
  have hfinA : (A.map q : Set (G ⧸ N)).Finite := (Set.toFinite (A : Set G)).image q
  have hfinB : (B.map q : Set (G ⧸ N)).Finite := (Set.toFinite (B : Set G)).image q
  let : Finite ((A.map q : Set (G ⧸ N)) * (B.map q : Set (G ⧸ N))) :=
    (hfinA.mul hfinB).to_subtype
  have hcard := Nat.card_le_card_of_injective
    (Set.inclusion hm) (Set.inclusion_injective hm)
  have hprod := Set.natCard_mul_le (s := (A.map q : Set (G ⧸ N))) (t := (B.map q : Set (G ⧸ N)))
  have hi : N = q.ker := (QuotientGroup.ker_mk' N).symm
  rw [hi,relIndex_ker,relIndex_ker,relIndex_ker]
  exact hcard.trans hprod
end Subgroup
