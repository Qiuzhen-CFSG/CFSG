module
public import Mathlib.GroupTheory.IndexNormal

/-!
# Intersecting an index-two subgroup

If H has index two in G and K is not contained in H, their intersection,
viewed as the actual subgroup H.subgroupOf K, has index two in K. This
standard index calculation supports subgroup analysis in ABG Chapter II,
Section 1, with no quasi-dihedral assumptions in its interface.

An index-two subgroup is normal, so its relative index divides its ambient
index. The only alternatives are one and two, and relative index one would
mean K is contained in H.
-/

/-- Restricting an index-two subgroup to a subgroup crossing its other coset
still gives index two. -/
public theorem Subgroup.subgroupOf_index_eq_two {G : Type*} [Group G]
    (H K : Subgroup G) (hH : H.index = 2) (hK : ¬ K ≤ H) :
    (H.subgroupOf K).index = 2 := by
  let := H.normal_of_index_eq_two hH
  have hd : H.relIndex K ∣ 2 := hH ▸ H.relIndex_dvd_index_of_normal K
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact (hK (Subgroup.relIndex_eq_one.mp h)).elim
  · exact h

