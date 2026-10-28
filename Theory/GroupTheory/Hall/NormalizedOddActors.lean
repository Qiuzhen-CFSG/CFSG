module

public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# An odd Hall subgroup preserved by odd solvable actors

An odd solvable subgroup A normalizing a solvable subgroup N preserves some
odd Hall subgroup D of N containing A intersect N. Apply Hall existence to
the solvable product NA, choosing a Hall subgroup E containing A. Then
D = E intersect N is Hall in N and is normalized by A.

This requires no coprimality between A and N. It supplies the invariant
odd Hall subgroup in Aschbacher--Smith, 10.2.3, printed p.745.
-/

public section
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]

theorem exists_actor_invariant_hall (N A : Subgroup G)
    [Group.IsSolvable N] [Group.IsSolvable A]
    (hAN : A ≤ normalizer (N : Set G)) (ho : Odd (Nat.card A)) :
    ∃ D : Subgroup G, D ≤ N ∧ IsHallSubgroup oddPrimes (D.subgroupOf N) ∧
      A ≤ normalizer (D : Set G) ∧ A ⊓ N ≤ D := by
  let K := N ⊔ A
  have hKN : K ≤ normalizer (N : Set G) := sup_le N.le_normalizer hAN
  obtain ⟨E,hAE,hEK,hE⟩ := exists_hall_containing_odd K A
    (Group.isSolvable_sup_of_normalizes N A hAN) le_sup_right ho
  refine ⟨E ⊓ N,inf_le_right,?_,?_,inf_le_inf hAE le_rfl⟩
  · rw [inf_subgroupOf_right]
    exact hall_restrict_of_normalizes hE hEK le_sup_left (hEK.trans hKN)
  · exact (le_inf (hAE.trans E.le_normalizer) hAN).trans
      inf_normalizer_le_normalizer_inf

end Subgroup.OddHall
