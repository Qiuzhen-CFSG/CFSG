module

public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Mathlib.Data.Set.Card

/-!
# Maximal two-local overgroups

The family below is `M(U)` in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined 1 March 2004 manuscript, Notation 1.0.1, p. 499.
Its members are maximal among two-local subgroups, rather than among all
proper subgroups. A nonidentity two-subgroup has such an overgroup: extend
its normalizer to a maximal two-local. The same conclusion for a subgroup
with nontrivial two-core is supplied by `TwoLocalCoreObstruction`.
-/

@[expose] public section

namespace Theory.GroupTheory

variable {G : Type*} [Group G]

/-- The maximal two-local subgroups containing `U`. -/
def maximalTwoLocalOvergroups (U : Subgroup G) : Set (Subgroup G) :=
  {M | IsMaximalTwoLocal M ∧ U ≤ M}

/-- Normalizing a nonidentity two-subgroup supplies a maximal two-local
overgroup. The nonidentity hypothesis is essential. -/
theorem maximalTwoLocalOvergroups_nonempty_of_isPGroup [Finite G]
    (U : Subgroup G) (hne : U ≠ ⊥) (hp : IsPGroup 2 U) :
    (maximalTwoLocalOvergroups U).Nonempty := by
  have hN : IsTwoLocal (Subgroup.normalizer (U : Set G)) := ⟨U, hne, hp, rfl⟩
  obtain ⟨M, hNM, hM⟩ := Finite.exists_le_maximal hN
  exact ⟨M, hM, U.le_normalizer.trans hNM⟩

/-- A subgroup with nontrivial two-core has a maximal two-local overgroup. -/
theorem maximalTwoLocalOvergroups_nonempty_of_twoCore_ne_bot [Finite G]
    (U : Subgroup G) (hU : pCore 2 U ≠ ⊥) :
    (maximalTwoLocalOvergroups U).Nonempty :=
  exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot U hU

/-- The source's numerical condition `|M(U)| = 1` is exactly uniqueness
of a maximal two-local overgroup. -/
theorem maximalTwoLocalOvergroups_ncard_eq_one_iff (U : Subgroup G) :
    (maximalTwoLocalOvergroups U).ncard = 1 ↔
      ∃! M, IsMaximalTwoLocal M ∧ U ≤ M := by
  rw [Set.ncard_eq_one]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_, ?_⟩
    · exact show M ∈ maximalTwoLocalOvergroups U from hM ▸ Set.mem_singleton M
    · intro N hN
      exact Set.mem_singleton_iff.mp (hM ▸ hN)
  · rintro ⟨M, hM, hu⟩
    refine ⟨M, Set.ext fun N => ?_⟩
    exact ⟨fun hN => Set.mem_singleton_iff.mpr (hu N hN),
      fun hN => Set.mem_singleton_iff.mp hN ▸ hM⟩

end Theory.GroupTheory
