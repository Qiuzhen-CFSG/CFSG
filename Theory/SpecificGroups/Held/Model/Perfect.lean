module

public import Theory.SpecificGroups.Held.Model.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Perfectness of the concrete Held group

The checked relations `a² = b⁷ = (ab)¹⁷ = 1` force both generator images
in any abelian group to be trivial: the product has order dividing both
14 and 17; then the first generator has order dividing both 2 and 7.
Generation by `a,b` makes the abelianization trivial. Together with the
already checked nontriviality this also proves nonsolvability.

Source: the first three relations of John Bray's ATLAS presentation
`HeG1-P1`, retained in `Model/Source/HeG1-P1.M`.
-/

namespace Held

private theorem triangle_abelian_trivial {A : Type*} [CommGroup A]
    (x y : A) (hx : x ^ 2 = 1) (hy : y ^ 7 = 1)
    (hxy : (x * y) ^ 17 = 1) : x = 1 ∧ y = 1 := by
  have h14 : (x * y) ^ 14 = 1 := by
    rw [mul_pow]
    have hx14 : x ^ 14 = 1 := by
      rw [show 14 = 2 * 7 from rfl, pow_mul, hx, one_pow]
    have hy14 : y ^ 14 = 1 := by
      rw [show 14 = 7 * 2 from rfl, pow_mul, hy, one_pow]
    rw [hx14, hy14, one_mul]
  have hprod : x * y = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h14)
      (orderOf_dvd_of_pow_eq_one hxy)
  have hx7 : x ^ 7 = 1 := by
    calc
      x ^ 7 = (x * y) ^ 7 := by rw [mul_pow, hy, mul_one]
      _ = 1 := by rw [hprod, one_pow]
  have hx1 : x = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx)
      (orderOf_dvd_of_pow_eq_one hx7)
  exact ⟨hx1, by simpa only [hx1, one_mul] using hprod⟩

/-- Every homomorphism from the concrete Held group to an abelian group is trivial.
The orders 2, 7, 17 force both generator images to be trivial. -/
public theorem hom_to_commGroup_trivial {A : Type*} [CommGroup A] (f : He →* A)
    (g : He) : f g = 1 := by
  obtain ⟨ha, hb⟩ := triangle_abelian_trivial (f a) (f b)
    (by simpa using congrArg f a_sq)
    (by simpa using congrArg f b_pow_seven)
    (by simpa using congrArg f ab_pow_seventeen)
  have hker : (⊤ : Subgroup He) ≤ f.ker := by
    rw [← closure_pair, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · exact (Set.mem_singleton_iff.mp hx) ▸ hb
  exact hker (Subgroup.mem_top g)

/-- Perfectness is intrinsic to the constructed group, using its generating
pair and the checked (2,7,17) relations. -/
public instance : Group.IsPerfect He where
  commutator_eq_top := by
    apply top_unique
    intro g _
    rw [← Abelianization.ker_of He]
    exact hom_to_commGroup_trivial Abelianization.of g

/-- A nontrivial perfect group is not solvable. -/
public theorem not_isSolvable : ¬ Group.IsSolvable He := Group.IsPerfect.not_isSolvable He

end Held
