module

public import Theory.GroupTheory.MaximalTwoLocalOvergroups

/-!
# Maximal two-local overgroups of centralizers

The centralizer of a nonidentity two-subgroup lies in its normalizer, hence
in a maximal two-local subgroup. Its overgroup family is therefore nonempty.
If a subgroup T centralizes that two-subgroup, uniqueness supplies a member
of M(T); otherwise the centralizer has at least two maximal two-local overgroups.

This supplies the coverage argument in Aschbacher–Smith, combined manuscript
(1 March 2004), proof of Theorem 15.4.25, printed p.1165.
-/

@[expose] public section

open Subgroup

namespace Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- A nonidentity two-subgroup gives its centralizer a maximal two-local overgroup. -/
theorem maximalTwoLocalOvergroups_centralizer_nonempty
    {Z : Subgroup G} (hne : Z ≠ ⊥) (hp : IsPGroup 2 Z) :
    (maximalTwoLocalOvergroups (centralizer (Z : Set G))).Nonempty := by
  have hN : IsTwoLocal (normalizer (Z : Set G)) := ⟨Z, hne, hp, rfl⟩
  obtain ⟨M, hNM, hM⟩ := Finite.exists_le_maximal hN
  exact ⟨M, hM, (Subgroup.centralizer_le_normalizer _).trans hNM⟩

/-- Coverage excludes the empty-family case before inferring uniqueness. -/
theorem maximalTwoLocalOvergroups_centralizer_cases
    {T Z : Subgroup G} (hne : Z ≠ ⊥) (hp : IsPGroup 2 Z)
    (hT : T ≤ centralizer (Z : Set G)) :
    (∃ M ∈ maximalTwoLocalOvergroups T,
      maximalTwoLocalOvergroups (centralizer (Z : Set G)) = {M}) ∨
      1 < (maximalTwoLocalOvergroups (centralizer (Z : Set G))).ncard := by
  have hpos := (maximalTwoLocalOvergroups_centralizer_nonempty hne hp).ncard_pos
  by_cases hone : (maximalTwoLocalOvergroups (centralizer (Z : Set G))).ncard = 1
  · obtain ⟨M, hM⟩ := Set.ncard_eq_one.mp hone
    have hm : M ∈ maximalTwoLocalOvergroups (centralizer (Z : Set G)) := by
      rw [hM]
      exact Set.mem_singleton M
    exact Or.inl ⟨M, ⟨hm.1, hT.trans hm.2⟩, hM⟩
  · exact Or.inr (by omega)

end Theory.GroupTheory

