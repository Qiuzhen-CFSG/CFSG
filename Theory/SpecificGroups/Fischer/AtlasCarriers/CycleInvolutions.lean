module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleEncoding
public import Mathlib.GroupTheory.Perm.Support

/-!
# Involutions from disjoint cycle tables

A decimal cycle table whose cycles are disjoint pairs decodes to a permutation
with square one. The proof uses disjointness to commute the transpositions;
thus data certificates need only check the flattened list for repetitions and
each cycle's length. No enumeration of the generated group is required.

This supports the first-generator calculation for the ATLAS Fi22 carrier;
see the data attribution in `CycleEncoding` and GLS3, Table 5.3t.
-/

public section

namespace Sporadic.Fischer.AtlasCarriers

private theorem formPerm_disjoint {n : ℕ} {a b : List (Fin n)} (h : a.Disjoint b) :
    a.formPerm.Disjoint b.formPerm := by
  intro i
  by_cases hi : i ∈ a
  · exact Or.inr (List.formPerm_apply_of_notMem (h hi))
  · exact Or.inl (List.formPerm_apply_of_notMem hi)

private theorem formPerm_pow_two {n : ℕ} (l : List (Fin n)) (h : l.length = 2) :
    l.formPerm ^ 2 = 1 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp_all [pow_two]

private theorem prod_pow_two {n : ℕ} (l : List (Equiv.Perm (Fin n)))
    (hd : l.Pairwise Equiv.Perm.Disjoint) (h : ∀ p ∈ l, p ^ 2 = 1) :
    l.prod ^ 2 = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hd
    rw [List.prod_cons, (Equiv.Perm.disjoint_prod_right l ha).commute.mul_pow,
      h a List.mem_cons_self, ih hl (fun p hp => h p (List.mem_cons_of_mem a hp)), mul_one]

/-- Disjoint transposition tables decode to elements whose square is one. -/
theorem permutationFromCycleBlocks_sq_eq_one {n : ℕ} [NeZero n] (blocks : List String)
    (hd : (decodeCycleBlocks n blocks).flatten.Nodup)
    (hl : ∀ l ∈ decodeCycleBlocks n blocks, l.length = 2) :
    permutationFromCycleBlocks n blocks ^ 2 = 1 := by
  have hp := (List.nodup_flatten.mp hd).2
  have hq : ((decodeCycleBlocks n blocks).map List.formPerm).prod ^ 2 = 1 := by
    apply prod_pow_two
    · exact List.pairwise_map.mpr (hp.imp formPerm_disjoint)
    · intro p hp
      obtain ⟨l, hm, rfl⟩ := List.mem_map.mp hp
      exact formPerm_pow_two l (hl l hm)
  simpa only [permutationFromCycleBlocks, inv_pow, inv_eq_one] using hq

end Sporadic.Fischer.AtlasCarriers

