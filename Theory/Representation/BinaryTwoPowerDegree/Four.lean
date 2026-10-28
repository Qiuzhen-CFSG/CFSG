module

public import Theory.Representation.BinaryTwoPowerDegree
public import Mathlib.Tactic.NormNum

/-!
# Order-eight obstruction in binary degree four

An element whose order is divisible by eight has a power of order eight.
The nilpotent dimension bound makes that power have fourth power one in a
faithful characteristic-two representation of degree at most four. The
obstruction passes to every homomorphic image and hence every section.

This is used for the PSU₄ row of the M₂₂-cover comparison in
Aschbacher--Smith 4.2.13, printed p.612.
-/

public section
namespace Representation.BinaryTwoPowerDegree
open Module LinearMap
variable {F G V : Type*} [Field F] [CharP F 2] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (ρ : Representation F G V) (hf : Function.Injective ρ)

include hf in
/-- Every image of a finite group with a faithful binary action of degree at
most four has no element of order eight. -/
theorem image_order_ne_eight [Finite G] (hd : finrank F V ≤ 4)
    {H : Type*} [Monoid H] (f : G →* H) (g : G) : orderOf (f g) ≠ 8 := by
  intro he
  have hdvd : 8 ∣ orderOf g := he ▸ orderOf_map_dvd f g
  let x := g ^ (orderOf g / 8)
  have hx : orderOf x = 8 := orderOf_pow_orderOf_div (orderOf_pos g).ne' hdvd
  have hp : x ^ (2 ^ 3) = 1 := by simpa only [hx,Nat.reducePow] using pow_orderOf_eq_one x
  have h4 := pow_eq_one_of_finrank_le ρ hf (m := 2) hd x hp
  have hh := orderOf_dvd_of_pow_eq_one h4
  norm_num [hx] at hh
end Representation.BinaryTwoPowerDegree
