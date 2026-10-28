module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Index

/-!
# Perfect subgroups in local group arguments

A perfect subgroup is contained in every subgroup of index at most two and in
every normal subgroup with solvable quotient. Its nontrivial images cannot lie
in solvable subgroups. These reductions apply to the component normalizers and
Borel subgroups in Aschbacher–Smith, *The Classification of Quasithin Groups*,
§C.4, pp. 151–152 (1 March 2004 manuscript).

The index-two assertion follows by putting each commutator in the subgroup.
The other assertions use preservation of perfectness under homomorphisms and
the incompatibility of perfectness and solvability in a nontrivial group.
-/

namespace Subgroup

variable {G D : Type*} [Group G] [Group D]

/-- Every perfect subgroup lies in every subgroup of index two. -/
public theorem le_of_isPerfect_of_index_eq_two (M N : Subgroup G)
    [Group.IsPerfect M] (hN : N.index = 2) : M ≤ N := by
  rw [← M.commutator_eq_self]
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  simp only [commutatorElement_def, N.mul_mem_iff_of_index_two hN, N.inv_mem_iff]
  tauto

/-- Every perfect subgroup of a finite group lies in every subgroup of index
at most two. -/
public theorem le_of_isPerfect_of_index_le_two [Finite G] (M N : Subgroup G)
    [Group.IsPerfect M] (hN : N.index ≤ 2) : M ≤ N := by
  have hpos := N.index_ne_zero_of_finite
  have hcases : N.index = 1 ∨ N.index = 2 := by omega
  rcases hcases with h | h
  · rw [Subgroup.index_eq_one.mp h]
    exact le_top
  · exact le_of_isPerfect_of_index_eq_two M N h

/-- A perfect subgroup has trivial image in a solvable quotient. -/
public theorem le_of_isPerfect_of_solvable_quotient (M N : Subgroup G)
    [Group.IsPerfect M] [N.Normal] [Group.IsSolvable (G ⧸ N)] : M ≤ N := by
  have hmap : M.map (QuotientGroup.mk' N) = ⊥ := by
    let : Group.IsPerfect (M.map (QuotientGroup.mk' N)) :=
      Group.IsPerfect.map _
    by_contra h
    let := (Subgroup.nontrivial_iff_ne_bot _).mpr h
    exact Group.IsPerfect.not_isSolvable (M.map (QuotientGroup.mk' N)) inferInstance
  simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hmap

/-- A nontrivial image of a perfect subgroup cannot lie in a solvable subgroup. -/
public theorem map_not_le_of_isPerfect_of_isSolvable (M : Subgroup G)
    [Group.IsPerfect M] (f : G →* D) (hM : ¬ M ≤ f.ker)
    (B : Subgroup D) [Group.IsSolvable B] : ¬ M.map f ≤ B := by
  intro hle
  let : Group.IsPerfect (M.map f) := Group.IsPerfect.map f
  let : Nontrivial (M.map f) := (Subgroup.nontrivial_iff_ne_bot _).mpr
    (fun h => hM ((Subgroup.map_eq_bot_iff M).mp h))
  let : Group.IsSolvable (M.map f) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable (M.map f) inferInstance

end Subgroup
