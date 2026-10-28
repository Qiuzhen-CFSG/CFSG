module

public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Solvable subgroups of index at most four

The action on cosets has solvable image in the symmetric group on at most
four letters. Its kernel lies in the given solvable subgroup, so the whole
group is solvable. The relative-index version applies even when neither of
the two ambient subgroups contains the other.

This is the small permutation action used for the nonabelian case of
Aschbacher–Smith, Lemma A.3.21(c), printed pp. 55–56.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A finite group with a solvable subgroup of index at most four is solvable. -/
theorem isSolvable_of_index_le_four (H : Subgroup G) [Group.IsSolvable H]
    (hi : H.index ≤ 4) : Group.IsSolvable G := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  change Nat.card (G ⧸ H) ≤ 4 at hi
  have hc : Fintype.card (G ⧸ H) ≤ Fintype.card (Fin 4) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hi
  let e : (G ⧸ H) ↪ Fin 4 :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (G ⧸ H)) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  apply Group.isSolvable_of_ker_le_range H.subtype (MulAction.toPermHom G (G ⧸ H))
  rw [range_subtype, ← H.normalCore_eq_ker]
  exact H.normalCore_le

/-- A subgroup meeting a solvable subgroup in index at most four is solvable. -/
theorem isSolvable_of_relIndex_le_four (H K : Subgroup G) [Group.IsSolvable H]
    (hi : H.relIndex K ≤ 4) : Group.IsSolvable K := by
  let f : H.subgroupOf K →* H := K.subtype.subgroupComap H
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => (z : G)) h
  let : Group.IsSolvable (H.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective hf
  exact (H.subgroupOf K).isSolvable_of_index_le_four hi

end Subgroup
