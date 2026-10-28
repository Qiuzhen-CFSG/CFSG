module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Two-power element orders in small characteristic-two representations

For a faithful characteristic-two action of degree at most `2^m`, every
element of two-power order has `2^m`-th power one. Subtracting the identity
turns the action into a nilpotent endomorphism, whose kernels stabilize by
the dimension. In degree at most eight this excludes an element of order
sixteen, also in every homomorphic image of a finite acting group.

The degree-eight case removes diagonal outer actors in the PSL₂(17)
calculation of Guralnick--Malle, *Classification of 2F-modules I*,
Proposition 4.1, used in Aschbacher--Smith K.2, printed p.453.
-/

public section
namespace Representation.BinaryTwoPowerDegree
open Module LinearMap

variable {F G V : Type*} [Field F] [CharP F 2] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (ρ : Representation F G V) (hf : Function.Injective ρ)
include hf

/-- Nilpotent kernel stabilization bounds the exponent of every two-element. -/
theorem pow_eq_one_of_finrank_le {m n : ℕ} (hd : finrank F V ≤ 2 ^ m)
    (g : G) (hg : g ^ (2 ^ n) = 1) : g ^ (2 ^ m) = 1 := by
  cases subsingleton_or_nontrivial V with
  | inl hV =>
    let := hV
    apply hf
    exact Subsingleton.elim _ _
  | inr hV =>
    let := hV
    let : CharP (Module.End F V) 2 := charP_of_injective_algebraMap' F 2
    have hn : (ρ g - 1) ^ (2 ^ n) = 0 := by
      rw [sub_pow_char_pow_of_commute 2 n (Commute.one_right (ρ g)),
        one_pow, ← map_pow, hg, map_one, sub_self]
    have hk := Module.End.ker_pow_le_ker_pow_finrank (ρ g - 1) (2 ^ n)
    rw [hn, LinearMap.ker_zero] at hk
    have hm : (ρ g - 1) ^ (2 ^ m) = 0 := by
      apply LinearMap.ker_eq_top.mp
      rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hd]
      exact top_le_iff.mp hk
    apply hf
    rw [map_pow, map_one]
    apply sub_eq_zero.mp
    simpa only [sub_pow_char_pow_of_commute 2 m (Commute.one_right (ρ g)), one_pow] using hm

/-- A faithful action of degree at most eight has no element of order sixteen. -/
theorem order_ne_sixteen (hd : finrank F V ≤ 8) (g : G) : orderOf g ≠ 16 := by
  intro hg
  have hp : g ^ (2 ^ 4) = 1 := by
    simpa only [show 2 ^ 4 = 16 by decide, hg] using pow_orderOf_eq_one g
  have h8 := pow_eq_one_of_finrank_le ρ hf (m := 3) hd g hp
  have hdiv := orderOf_dvd_of_pow_eq_one h8
  norm_num [hg] at hdiv

/-- The same obstruction detects sixteen as a divisor of an element order. -/
theorem sixteen_not_dvd_order [Finite G] (hd : finrank F V ≤ 8) (g : G) :
    ¬ 16 ∣ orderOf g := by
  intro hdiv
  exact order_ne_sixteen ρ hf hd _
    (orderOf_pow_orderOf_div (orderOf_pos g).ne' hdiv)

/-- In particular no quotient or action image contains an order-sixteen image. -/
theorem image_order_ne_sixteen [Finite G] (hd : finrank F V ≤ 8)
    {H : Type*} [Monoid H] (f : G →* H) (g : G) : orderOf (f g) ≠ 16 := by
  intro hg
  apply sixteen_not_dvd_order ρ hf hd g
  simpa only [hg] using orderOf_map_dvd f g

end Representation.BinaryTwoPowerDegree
