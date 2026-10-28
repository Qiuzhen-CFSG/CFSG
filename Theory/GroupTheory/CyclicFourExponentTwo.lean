module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Exponent-two images of a cyclic quotient of order four

Suppose a homomorphism g kills the kernel of a surjection f onto a cyclic
group of order four, and every value of g has square one. Then g kills
every element whose f-image has square one. Indeed, such an image is an
even power of a generator; lifting that generator reduces the assertion
to the exponent-two condition.
-/

open Subgroup

namespace MonoidHom

/-- An exponent-two homomorphism through a cyclic quotient of order four
kills the preimage of its square-one elements. -/
public theorem eq_one_of_cyclic_four_of_square_eq_one {P C A : Type*} [Group P] [Group C] [Finite C] [IsCyclic C]
    [CommGroup A] (f : P →* C) (hf : Function.Surjective f)
    (hC : Nat.card C = 4) (g : P →* A)
    (hker : f.ker ≤ g.ker) (hsq : ∀ x, (g x) ^ 2 = 1)
    (x : P) (hx : (f x) ^ 2 = 1) : g x = 1 := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_monoid_generator (α := C)
  have hord : orderOf u = 4 := (orderOf_eq_card_of_forall_mem_powers hu).trans hC
  obtain ⟨y, hy⟩ := hf u
  obtain ⟨n, hn⟩ := hu (f x)
  change u ^ n = f x at hn
  have hdiv : 4 ∣ n * 2 := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, pow_mul, hn]
    exact hx
  have heven : 2 ∣ n := by omega
  obtain ⟨k, hk⟩ := heven
  have hxy : x / y ^ n ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_div, map_pow, hy, hn, div_self']
  have hgeq : g x = (g y) ^ n := by
    have hh := hker hxy
    have hh' : g x / (g y) ^ n = 1 := by
      simpa only [MonoidHom.mem_ker, map_div, map_pow] using hh
    exact div_eq_one.mp hh'
  rw [hgeq, hk, pow_mul, hsq, one_pow]

end MonoidHom
