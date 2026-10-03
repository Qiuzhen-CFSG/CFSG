module

public import Theory.Frattini.PGroupMap
public import Theory.GroupTheory.PGroup.MaximalIndex
public import Mathlib.GroupTheory.Index

/-!
# The second Frattini subgroup and index four

Every subgroup of index four in a finite two-group contains the image of the
Frattini subgroup of the ambient Frattini subgroup. Choose a maximal subgroup
above the given subgroup. Both steps have index two; apply the maximal-subgroup
property of Frattini and its functoriality for finite p-groups.

This is a direct consequence of the standard Frattini results in
`Theory.Frattini.PGroupMap` and the maximal-index theorem.
-/

namespace Subgroup
/-- Every index-four subgroup of a finite two-group contains its second Frattini subgroup. -/
public theorem second_frattini_le_of_index_eq_four {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (U : Subgroup G) (hU : U.index = 4) :
    (frattini (frattini G)).map (frattini G).subtype ≤ U := by
  have hne : U ≠ ⊤ := by intro h; simp [h] at hU
  obtain ⟨M, hM, hUM⟩ := (eq_top_or_exists_le_coatom U).resolve_left hne
  have hMi : M.index = 2 := hG.index_of_isCoatom M hM
  have hrel : (U.subgroupOf M).index = 2 := by
    have h := relIndex_mul_index hUM
    rw [hMi, hU] at h
    change U.relIndex M = 2
    omega
  have hco : IsCoatom (U.subgroupOf M) := by
    refine ⟨?_, ?_⟩
    · intro h; simp [h] at hrel
    · intro B hB
      have hb := index_strictAnti hB
      have hz := B.index_ne_zero_of_finite
      rw [hrel] at hb
      exact index_eq_one.mp (by omega)
  have hphiM : frattini G ≤ M := frattini_le_coatom hM
  let : Fact (IsPGroup 2 M) := ⟨hG.to_subgroup M⟩
  let : Fact (IsPGroup 2 (frattini G)) := ⟨hG.to_subgroup _⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact frattini_le_coatom hco
    (frattini_map_le_of_isPGroup (p := 2) (inclusion hphiM)
      (mem_map_of_mem _ hy))
end Subgroup
