module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace

/-!
# Fixed vectors for the disjoint-transposition groups

For `A_m`, all four binary permutation sections have the same coordinate
condition on representatives: the coordinates in each swapped pair agree.
For the quotient sections this uses a third point fixed by each generator;
it does not assume that the whole subgroup has a common fixed point.
Dimension differences still arise from the augmentation and constant line.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(1), printed p. 84.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders

open BinaryPermutation Representation.BinaryOffender

/-- Each generating transposition has a fixed point as soon as `n ≥ 3`. -/
theorem pairSwap_has_fixed_point {n : ℕ} (hn : 3 ≤ n) (i : Fin (n / 2)) :
    ∃ k : Fin n, pairSwap n i k = k := by
  by_cases hi : i.val = 0
  · refine ⟨⟨2, by omega⟩, ?_⟩
    apply Equiv.swap_apply_of_ne_of_ne <;>
      (intro h; have := congrArg Fin.val h; dsimp at this; omega)
  · refine ⟨⟨0, by omega⟩, ?_⟩
    apply Equiv.swap_apply_of_ne_of_ne <;>
      (intro h; have := congrArg Fin.val h; dsimp at this; omega)

/-- Fixed representatives in the full module. -/
theorem full_fixed_disjointTranspositions_iff (n m : ℕ) (v : Full (Fin n)) :
    v ∈ fixedSpace (representation (Fin n)) (disjointTranspositions n m) ↔
      ∀ i : Fin (n / 2), i.val < m →
        v ⟨2 * i.val, by omega⟩ = v ⟨2 * i.val + 1, by omega⟩ := by
  rw [disjointTranspositions, mem_fixedSpace_closure_iff]
  constructor
  · intro h i hi
    exact (swap_fixed_iff _ _ v).mp (h _ ⟨i, hi, rfl⟩)
  · rintro h g ⟨i, hi, rfl⟩
    exact (swap_fixed_iff _ _ v).mpr (h i hi)

/-- Fixed representatives in the core. -/
theorem core_fixed_disjointTranspositions_iff (n m : ℕ) (v : core (Fin n)) :
    v ∈ fixedSpace (coreRepresentation (Fin n)) (disjointTranspositions n m) ↔
      ∀ i : Fin (n / 2), i.val < m →
        v.val ⟨2 * i.val, by omega⟩ = v.val ⟨2 * i.val + 1, by omega⟩ := by
  rw [mem_core_fixedSpace_iff, ← mem_full_fixedSpace_iff,
    full_fixed_disjointTranspositions_iff]

/-- No extra fixed representatives appear for `A_m` in the deleted module. -/
theorem deleted_fixed_disjointTranspositions_iff {n : ℕ} (hn : 3 ≤ n)
    (m : ℕ) (v : Full (Fin n)) :
    (constants (Fin n)).mkQ v ∈
      fixedSpace (deletedRepresentation (Fin n)) (disjointTranspositions n m) ↔
      ∀ i : Fin (n / 2), i.val < m →
        v ⟨2 * i.val, by omega⟩ = v ⟨2 * i.val + 1, by omega⟩ := by
  rw [disjointTranspositions, mem_fixedSpace_closure_iff]
  have hi (i : Fin (n / 2)) :
      deletedRepresentation (Fin n) (pairSwap n i) ((constants (Fin n)).mkQ v) =
          (constants (Fin n)).mkQ v ↔
        v ⟨2 * i.val, by omega⟩ = v ⟨2 * i.val + 1, by omega⟩ := by
    obtain ⟨k, hk⟩ := pairSwap_has_fixed_point hn i
    rw [deleted_fixed_iff_of_fixed_point _ _ k hk]
    exact swap_fixed_iff _ _ v
  constructor
  · intro h i him
    exact (hi i).mp (h _ ⟨i, him, rfl⟩)
  · rintro h g ⟨i, him, rfl⟩
    exact (hi i).mpr (h i him)

/-- Fixed representatives in the natural section. -/
theorem natural_fixed_disjointTranspositions_iff {n : ℕ} (hn : 3 ≤ n)
    (m : ℕ) (v : core (Fin n)) :
    (⟨(constants (Fin n)).mkQ v.val, ⟨v.val, v.property, rfl⟩⟩ : natural (Fin n)) ∈
      fixedSpace (naturalRepresentation (Fin n)) (disjointTranspositions n m) ↔
      ∀ i : Fin (n / 2), i.val < m →
        v.val ⟨2 * i.val, by omega⟩ = v.val ⟨2 * i.val + 1, by omega⟩ := by
  rw [mem_natural_fixedSpace_iff, ← mem_deleted_fixedSpace_iff,
    deleted_fixed_disjointTranspositions_iff hn]

end CFSG.Quasithin.ChapterB.Offenders
