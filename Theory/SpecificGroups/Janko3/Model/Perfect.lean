module

public import Theory.SpecificGroups.Janko3.Model.Relations
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Perfectness of the concrete J₃ model

The standard generators have orders 2 and 3, and their product has order 19.
In an abelian quotient the product has order dividing both 6 and 19, so the
product is trivial. Each generator then has order dividing both 2 and 3, and
is trivial. Since the pair generates, the abelianization is trivial.

This elementary argument uses only the certified ATLAS generator relations
from `Model.Relations`, not a simplicity or group-order assertion.
-/

namespace Sporadic.Janko3

/-- The explicit permutation group is perfect. -/
public instance model_perfect : Group.IsPerfect Model := by
  let f : Model →* Abelianization Model := Abelianization.of
  have ha : f a ^ 2 = 1 := by rw [← map_pow, a_sq, map_one]
  have hb : f b ^ 3 = 1 := by rw [← map_pow, b_cube, map_one]
  have hab6 : (f a * f b) ^ 6 = 1 := by
    rw [mul_pow]
    have ha6 : f a ^ 6 = 1 := by
      calc
        f a ^ 6 = (f a ^ 2) ^ 3 := (pow_mul _ 2 3)
        _ = 1 := by rw [ha, one_pow]
    have hb6 : f b ^ 6 = 1 := by
      calc
        f b ^ 6 = (f b ^ 3) ^ 2 := (pow_mul _ 3 2)
        _ = 1 := by rw [hb, one_pow]
    rw [ha6, hb6, one_mul]
  have hab19' : (f a * f b) ^ 19 = 1 := by
    rw [← map_mul, ← map_pow, ab_pow, map_one]
  have hab : f a * f b = 1 := orderOf_eq_one_iff.mp <|
    Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 6 19)
      (orderOf_dvd_of_pow_eq_one hab6) (orderOf_dvd_of_pow_eq_one hab19')
  have ha' : f a = (f b)⁻¹ := eq_inv_of_mul_eq_one_left hab
  have ha3 : f a ^ 3 = 1 := by rw [ha', inv_pow, hb, inv_one]
  have ha1 : f a = 1 := orderOf_eq_one_iff.mp <|
    Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
      (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one ha3)
  have hb1 : f b = 1 := by simpa [ha1] using hab
  constructor
  apply top_unique
  rw [← generators_closure, Subgroup.closure_le]
  intro x hx
  rw [← Abelianization.ker_of]
  change f x = 1
  rcases hx with rfl | hx
  · exact ha1
  · have he : x = b := hx
    exact he ▸ hb1

end Sporadic.Janko3
