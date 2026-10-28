module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Seed.Relations
public import Theory.GroupTheory.PGroup.GeneratorSeries

/-!
# The literal Held seed is a two-group

Finite certificates for the exact eight Held seed words from `../Source/seed_words.json`.
Sources: ATLAS HeG1-p2058B0; GLS3 Table 5.3p. The external discovery and
generation scripts only propose data; all identities are checked by Lean.
-/

namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Seed

private theorem conjugateWord_lt : ∀ (k j t : Fin 10),
    t ∈ conjugateWord k j → t.val < k.val := by decide +kernel

private theorem pcGenerator_normalizes_prefix (k : Fin 10) :
    pcGenerator k ∈ Subgroup.normalizer
      (Subgroup.generatorPrefix pcGenerator k.val : Set He) := by
  unfold Subgroup.generatorPrefix
  apply Subgroup.mem_normalizer_closure_of_conjugates
  rintro _ ⟨j, hj, rfl⟩
  rw [pcGenerator_conjugate k j hj]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure ⟨t, conjugateWord_lt k j t ht, rfl⟩

private theorem seedSubgroup_le_pcClosure :
    seedSubgroup ≤ Subgroup.closure (Set.range pcGenerator) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  rw [seedGenerator_eq_pcProduct]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (Set.mem_range_self j)

end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Seed

namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups

/-- The closure of the eight literal seed words is a two-group. The proof uses
an ascending normalizing series with cyclic factors of two-power order. -/
public theorem seedSubgroup_isPGroup : IsPGroup 2 seedSubgroup := by
  have hp := Subgroup.isPGroup_closure_of_normalizing_generators Seed.pcGenerator
    (fun i => ⟨2, Seed.pcGenerator_pow_four i⟩)
    Seed.pcGenerator_normalizes_prefix
  exact hp.of_injective (Subgroup.inclusion Seed.seedSubgroup_le_pcClosure)
    (Subgroup.inclusion_injective _)

end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups
