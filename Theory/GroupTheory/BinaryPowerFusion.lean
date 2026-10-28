module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.IntervalCases

/-!
# Binary power fusion for an element of fourth power one

For a character to the group of order two, conjugacy compatibility on an
order-dividing-four cyclic subgroup reduces to its generator and square.
The identity case is immediate, and inversion gives the third power from
the first. Reducing arbitrary exponents modulo four gives all powers.

This elementary reduction supplies the finite fusion checks in the
transfer argument at the upper endpoint of Stellmacher (10.1)(b).
-/

namespace Subgroup
universe u

/-- For a binary character and an element of fourth power one, ambient fusion
of the element and its square determines ambient fusion of all its powers. -/
public theorem binary_power_fusion_of_pow_four
    {G : Type u} [Group G] (S : Subgroup G)
    (χ : S →* Multiplicative (ZMod 2)) (x : S) (hx : x ^ 4 = 1)
    (hfirst : ∀ y : S, IsConj (x : G) (y : G) → χ y = χ x)
    (hsquare : ∀ y : S, IsConj (((x ^ 2) : S) : G) (y : G) → χ y = 1) :
    ∀ (n : ℕ) (y : S), IsConj (((x ^ n) : S) : G) (y : G) →
      χ y = χ (x ^ n) := by
  have htwo (a : Multiplicative (ZMod 2)) : a ^ 2 = 1 := by
    have hc : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
    simpa only [hc] using (pow_card_eq_one' (x := a))
  have hthree : x ^ 3 = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using hx
  intro n y hconj
  have hreduce : x ^ n = x ^ (n % 4) := by
    calc
      x ^ n = x ^ (n % 4 + 4 * (n / 4)) := congrArg (x ^ ·) (Nat.mod_add_div n 4).symm
      _ = x ^ (n % 4) := by rw [pow_add, pow_mul, hx, one_pow, mul_one]
  rw [hreduce] at hconj ⊢
  have hbound : n % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize hremainder : n % 4 = remainder at hconj ⊢ hbound
  interval_cases remainder
  · have hy : y = 1 := Subtype.ext (isConj_one_right.mp (by simpa using hconj))
    simp [hy]
  · simpa only [pow_one] using hfirst y (by simpa using hconj)
  · rw [hsquare y hconj, map_pow, htwo]
  · rw [hthree] at hconj ⊢
    have hinv : IsConj (x : G) ((y⁻¹ : S) : G) := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hconj
      apply isConj_iff.mpr
      refine ⟨g, ?_⟩
      have h := congrArg Inv.inv hg
      simpa [mul_assoc] using h
    have h := congrArg Inv.inv (hfirst y⁻¹ hinv)
    simpa only [map_inv, inv_inv] using h

end Subgroup
