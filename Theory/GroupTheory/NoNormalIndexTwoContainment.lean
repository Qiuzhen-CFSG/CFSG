module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Containment in normal subgroups of index two

A subgroup L with no normal subgroup of index two lies in every normal
index-two subgroup K of the ambient group. No finiteness hypothesis is needed:
the index of the inverse image of K in L divides two, so exclusion of index
two forces that inverse image to be all of L.

This is the containment step for the normal PSL2 subgroup in ABG Chapter II,
Section 3, Proposition 2, article p22 of the Alperin--Brauer--Gorenstein paper.
It isolates the elementary deduction from the preceding classification step.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup without normal subgroups of index two lies in every ambient
normal subgroup of index two. -/
public theorem le_of_no_normal_index_two
    (L K : Subgroup G) [K.Normal] (hK : K.index = 2)
    (hL : ∀ N : Subgroup L, N.Normal → N.index ≠ 2) : L ≤ K := by
  have hd : (K.subgroupOf L).index ∣ 2 := by
    simpa [hK, Subgroup.relIndex] using K.relIndex_dvd_index_of_normal (K := L)
  have hne : (K.subgroupOf L).index ≠ 2 := hL _ inferInstance
  have hi : (K.subgroupOf L).index = 1 :=
    (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right hne
  have ht : K.subgroupOf L = ⊤ := (Subgroup.index_eq_one).mp hi
  intro x hx
  exact show (⟨x, hx⟩ : L) ∈ K.subgroupOf L from ht.symm ▸ Subgroup.mem_top _

end Subgroup
