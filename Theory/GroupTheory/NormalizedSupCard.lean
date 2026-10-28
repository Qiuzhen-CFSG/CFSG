module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index

/-!
# Cardinality of a normalized disjoint subgroup product

If a subgroup `K` normalizes `H` and their intersection is trivial, the
cardinality of their join is the product of their cardinalities. No
finiteness hypothesis is needed for this disjoint case: the proof uses an equivalence of the
underlying types and `Nat.card`.

Multiplication maps `H × K` to `H ⊔ K`. Trivial intersection makes this map
injective, while normalization identifies the join with the set product
and makes it surjective. Transporting cardinality along this bijection
establishes the formula without assuming that the factors commute.

For finite groups a second theorem allows an arbitrary intersection. The
relative-index formula for a normalized join and the two cardinal-index
identities give |H|*|K|=|H∩K|*|H⊔K|. This form is also used in the quaternion
central-product and elementary-eight projection calculations in Stellmacher
(9.1), Journal of Algebra 190 (1997), p.48.

This is the product-order calculation used in Brauer, *On finite Desarguesian
planes I*, equation (2.7), article page 120. In that application it equates
the orders, and hence the indices, of the point and line stabilizers.
-/

open scoped Pointwise

namespace Subgroup

/-- A join of disjoint subgroups has product cardinality when the second
subgroup normalizes the first. -/
public theorem card_sup_eq_mul_of_normalizes_of_disjoint
    {G : Type*} [Group G] (H K : Subgroup G)
    (hn : K ≤ normalizer (H : Set G)) (hd : Disjoint H K) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let m : H × K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem_sup p.1.property p.2.property⟩
  have hi : Function.Injective m := fun _ _ h =>
    mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hs : Function.Surjective m := by
    intro x
    have hx : (x : G) ∈ (H : Set G) * (K : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left H K hn]
      exact x.property
    obtain ⟨h, hh, k, hk, hprod⟩ := hx
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hprod⟩
  calc
    Nat.card ↥(H ⊔ K) = Nat.card (H × K) :=
      (Nat.card_congr (Equiv.ofBijective m ⟨hi, hs⟩)).symm
    _ = Nat.card H * Nat.card K := Nat.card_prod H K

public theorem card_mul_eq_card_inf_mul_card_sup_of_normalizes {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (hn : C ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card B * Nat.card C = Nat.card (B ⊓ C : Subgroup G) * Nat.card (B ⊔ C : Subgroup G) := by
  let V := B ⊔ C
  let _ : (B.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hindex := Subgroup.relIndex_sup_left (C.subgroupOf V) (B.subgroupOf V)
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.relIndex_subgroupOf le_rfl,
    Subgroup.relIndex_subgroupOf le_sup_right] at hindex
  have hindex' : B.relIndex V = (B ⊓ C).relIndex C := by
    exact hindex.trans (Subgroup.inf_relIndex_right B C).symm
  have hcardV := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) B V bot_le le_sup_left
  have hcardC := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ C) C bot_le inf_le_right
  simp only [Subgroup.relIndex_bot_left] at hcardV hcardC
  rw [hindex'] at hcardV
  rw [← hcardC, ← hcardV]
  ac_rfl

end Subgroup
