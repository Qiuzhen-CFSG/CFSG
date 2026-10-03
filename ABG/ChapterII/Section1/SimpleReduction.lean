module

public import ABG.ChapterII.Section1.Noncommutative
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The simple-group reduction in the quasi-dihedral fusion alternatives

ABG Chapter II, Section 1, Proposition 1 (article page 10) separates groups
with quasi-dihedral Sylow 2-subgroups according to their normal subgroups of
index two. For a simple group, the alternatives having such a subgroup are
impossible. An index-two subgroup is normal and hence is bottom or top;
bottom would make the whole group cyclic of order two, contradicting the
noncommutativity of its quasi-dihedral Sylow subgroup. Top has index one.

This reduction supplies the absence of index-two subgroups. The fusion and
normalizer conclusions in Proposition 1(i) require the remaining fusion proof.
-/

namespace ABG.QuasiDihedral

/-- A simple group with a quasi-dihedral Sylow 2-subgroup has no subgroup
of index two. -/
public theorem index_ne_two {G : Type*} [Group G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (H : Subgroup G) : H.index ≠ 2 := by
  intro hindex
  rcases (H.normal_of_index_eq_two hindex).eq_bot_or_eq_top with rfl | rfl
  · rw [Subgroup.index_bot] at hindex
    have : IsCyclic G := isCyclic_of_prime_card hindex
    exact not_isMulCommutative hS inferInstance
  · simp at hindex

end ABG.QuasiDihedral
