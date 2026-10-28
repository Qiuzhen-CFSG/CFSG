module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Abelian index-three subgroups of finite three-groups

An abelian maximal subgroup of a nonabelian three-group is self-centralizing:
otherwise it is central, and its cyclic quotient would make the whole group
abelian. Two distinct abelian index-three subgroups generate the group and
intersect in its center. Multiplication of indices then gives center index nine.

These are the structural facts behind the normalizer-orbit bound in
Aschbacher–Smith, *The Classification of Quasithin Groups*, A.3.21(c),
printed pp.55–56 (`refs/quasithin.pdf`).
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A subgroup of index three is maximal. -/
public theorem isCoatom_of_index_three (A : Subgroup G) (hi : A.index = 3) :
    IsCoatom A := by
  refine ⟨fun ht => by simp [ht] at hi, fun B hAB => ?_⟩
  have hm := relIndex_mul_index hAB.le
  rw [hi] at hm
  have hp : (A.relIndex B * B.index).Prime := hm ▸ (by decide : Nat.Prime 3)
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hB⟩ | ⟨_, hrel⟩
  · exact index_eq_one.mp hB
  · exact (hAB.not_ge (relIndex_eq_one.mp hrel)).elim

/-- Index-three subgroups of finite three-groups are normal. -/
public theorem normal_of_index_three_of_isPGroup (hG : IsPGroup 3 G)
    (A : Subgroup G) (hi : A.index = 3) : A.Normal := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Group.IsNilpotent G := hG.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom A
    (Group.normalizerCondition_of_isNilpotent (G := G)) (isCoatom_of_index_three A hi)

/-- An abelian index-three subgroup of a nonabelian three-group is self-centralizing. -/
public theorem centralizer_eq_of_abelian_index_three (hG : IsPGroup 3 G)
    (hn : ¬ IsMulCommutative G) (A : Subgroup G)
    (ha : IsMulCommutative A) (hi : A.index = 3) : centralizer (A : Set G) = A := by
  let : IsMulCommutative A := ha
  rcases (isCoatom_of_index_three A hi).le_iff.mp A.le_centralizer with ht | he
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    let : A.Normal := normal_of_index_three_of_isPGroup hG A hi
    let : IsCyclic (G ⧸ A) := isCyclic_of_prime_card (by
      change A.index = 3
      exact hi)
    exact (hn ((QuotientGroup.mk' A).isMulCommutative_of_isCyclic_of_ker_le_center
      (by simpa using centralizer_eq_top_iff_subset.mp ht))).elim
  · exact he

/-- Every abelian index-three subgroup contains the center. -/
public theorem center_le_of_abelian_index_three (hG : IsPGroup 3 G)
    (hn : ¬ IsMulCommutative G) (A : Subgroup G)
    (ha : IsMulCommutative A) (hi : A.index = 3) : center G ≤ A := by
  rw [← centralizer_eq_of_abelian_index_three hG hn A ha hi]
  exact center_le_centralizer _

/-- Distinct abelian index-three subgroups intersect precisely in the center. -/
public theorem inf_eq_center_of_distinct_abelian_index_three (hG : IsPGroup 3 G)
    (hn : ¬ IsMulCommutative G) (A B : Subgroup G)
    (ha : IsMulCommutative A) (hb : IsMulCommutative B)
    (hi : A.index = 3) (hj : B.index = 3) (hne : A ≠ B) : A ⊓ B = center G := by
  let : IsMulCommutative A := ha
  let : IsMulCommutative B := hb
  have hsup := (isCoatom_of_index_three A hi).sup_eq_top_of_ne
    (isCoatom_of_index_three B hj) hne
  apply le_antisymm
  · have hAc : A ≤ centralizer (A ⊓ B : Set G) :=
      A.le_centralizer.trans (centralizer_le (show (A ⊓ B : Set G) ⊆ A from inf_le_left))
    have hBc : B ≤ centralizer (A ⊓ B : Set G) :=
      B.le_centralizer.trans (centralizer_le (show (A ⊓ B : Set G) ⊆ B from inf_le_right))
    have ht : centralizer (A ⊓ B : Set G) = ⊤ := top_unique (hsup ▸ sup_le hAc hBc)
    exact centralizer_eq_top_iff_subset.mp ht
  · exact le_inf (center_le_of_abelian_index_three hG hn A ha hi)
      (center_le_of_abelian_index_three hG hn B hb hj)

/-- Two distinct abelian index-three subgroups force the center to have index nine. -/
public theorem center_index_eq_nine_of_distinct_abelian_index_three (hG : IsPGroup 3 G)
    (hn : ¬ IsMulCommutative G) (A B : Subgroup G)
    (ha : IsMulCommutative A) (hb : IsMulCommutative B)
    (hi : A.index = 3) (hj : B.index = 3) (hne : A ≠ B) : (center G).index = 9 := by
  let : B.Normal := normal_of_index_three_of_isPGroup hG B hj
  have hsup := (isCoatom_of_index_three A hi).sup_eq_top_of_ne
    (isCoatom_of_index_three B hj) hne
  have hrel : (A ⊓ B).relIndex A = 3 := by
    rw [inf_relIndex_left, ← relIndex_sup_right A B, hsup, relIndex_top_right, hj]
  have hm := relIndex_mul_index (show A ⊓ B ≤ A from inf_le_left)
  rw [hrel, hi, inf_eq_center_of_distinct_abelian_index_three hG hn A B ha hb hi hj hne] at hm
  exact hm.symm
end Subgroup
