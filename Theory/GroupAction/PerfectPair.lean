module
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A perfect group cannot exchange a pair

An orbit contained in two points has stabilizer of index one or two.
The second case would give a nontrivial abelian quotient of a perfect group.
-/

public section
open Subgroup
namespace MulAction
variable {D Ω : Type*} [Group D] [Finite D] [Group.IsPerfect D] [MulAction D Ω]

/-- Every orbit of a finite perfect group contained in a pair is a singleton. -/
theorem fixed_of_isPerfect_pair (a b : Ω)
    (hpair : ∀ d : D, d • a = a ∨ d • a = b) (d : D) : d • a = a := by
  have horbit : orbit D a ⊆ ({a,b} : Set Ω) := by
    rintro y ⟨g,rfl⟩
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hpair g
  have hi : (stabilizer D a).index ≤ 2 := by
    rw [index_stabilizer]
    exact (Set.ncard_le_ncard horbit).trans (by simpa using Set.ncard_insert_le a {b})
  have hp := (stabilizer D a).index_ne_zero_of_finite
  have he : (stabilizer D a).index = 1 ∨ (stabilizer D a).index = 2 := by omega
  have ht : stabilizer D a = ⊤ := by
    rcases he with he | he
    · exact index_eq_one.mp he
    · let N := stabilizer D a
      let : N.Normal := normal_of_index_eq_two he
      have hc : Nat.card (D ⧸ N) = 2 := he
      let : IsCyclic (D ⧸ N) := isCyclic_of_prime_card hc
      have : Subsingleton (D ⧸ N) := by
        by_contra! hn
        exact Group.IsPerfect.not_isNilpotent (D ⧸ N) inferInstance
      have : (1 : ℕ) = 2 := by simpa only [Nat.card_unique] using hc
      omega
  exact (show d ∈ stabilizer D a by rw [ht]; trivial)

end MulAction
