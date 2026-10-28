module

public import Theory.GroupTheory.PerfectSmallTwoAction

/-!
# Perfect normalizers of small subgroups

A perfect subgroup centralizes any normalized subgroup of order at most four.
Restrict to their join, where the small subgroup is normal, and apply the
solvability of its permutation automorphism action. Map the resulting trivial
commutator back through the original inclusion.

This is the standard small perfect-action argument. Its source application is
the point-core containment in Aschbacher--Smith 12.5.8(1), printed p.820.
-/

public section

namespace Subgroup

/-- A perfect subgroup centralizes any subgroup of order at most four that it normalizes. -/
theorem commutator_eq_bot_of_perfect_normalizer_card_le_four
    {X : Type*} [Group X] [Finite X] (B A : Subgroup X) [Group.IsPerfect B]
    (hn : B ≤ normalizer (A : Set X)) (hc : Nat.card A ≤ 4) : ⁅B,A⁆ = ⊥ := by
  let J := B ⊔ A
  let E := A.subgroupOf J
  let F := B.subgroupOf J
  let : E.Normal := normal_subgroupOf_of_le_normalizer (sup_le hn A.le_normalizer)
  let b : F ≃* B := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect F := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  have hsmall : Nat.card E ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ J from le_sup_right)).toEquiv]
    exact hc
  have hz := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_of_isPerfect_of_card_le_four F E hsmall)
  have he := congrArg (map J.subtype) hz
  simpa only [F,E,map_commutator,
    map_subgroupOf_eq_of_le (show B ≤ J from le_sup_left),
    map_subgroupOf_eq_of_le (show A ≤ J from le_sup_right),Subgroup.map_bot] using he

end Subgroup

