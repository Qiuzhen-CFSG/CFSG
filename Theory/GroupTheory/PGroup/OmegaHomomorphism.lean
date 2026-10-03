module

public import Theory.GroupTheory.PGroup.Omega
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Homomorphisms on the first two-omega subgroup

A homomorphism into a commutative group sends every element of Ω₁ to an
element whose square is one. Also, to check that a homomorphism acts trivially
on Ω₁ modulo the derived subgroup, it suffices to check the square-one
generators. Both assertions follow from the defining closure of Ω₁.
-/

open Subgroup
open scoped IsMulCommutative

namespace MonoidHom

/-- The image of the first two-omega in a commutative group has exponent two. -/
public theorem square_eq_one_on_omega₁
    {G A : Type*} [Group G] [Group A] [IsMulCommutative A]
    (f : G →* A) {x : G} (hx : x ∈ omega₁ G (p := 2)) : (f x) ^ 2 = 1 := by
  refine closure_induction (p := fun x _ => (f x) ^ 2 = 1) ?_ ?_ ?_ ?_ hx
  · intro x hx
    change x ^ (2 ^ 1) = 1 at hx
    rw [← map_pow, show x ^ 2 = 1 from hx, map_one]
  · simp only [map_one, one_pow]
  · intro x y _ _ hx hy
    rw [map_mul, mul_pow, hx, hy, one_mul]
  · intro x _ hx
    rw [map_inv, inv_pow, hx, inv_one]

/-- Trivial displacement modulo the derived subgroup can be checked just
on the square-one generators of the first two-omega. -/
public theorem displacement_on_omega₁_iff
    {G : Type*} [Group G] (f : G →* G) :
    (∀ x ∈ omega₁ G (p := 2), x⁻¹ * f x ∈ commutator G) ↔
      (∀ x : G, x ^ 2 = 1 → x⁻¹ * f x ∈ commutator G) := by
  constructor
  · intro h x hx
    exact h x (subset_closure (show x ^ (2 ^ 1) = 1 from hx))
  · intro h x hx
    let q := QuotientGroup.mk' (commutator G)
    have heq : q (f x) = q x := by
      refine closure_induction (p := fun x _ => q (f x) = q x) ?_ ?_ ?_ ?_ hx
      · intro y hy
        have hh := (QuotientGroup.eq_one_iff (N := commutator G) _).mpr
          (h y (show y ^ 2 = 1 from hy))
        change q (y⁻¹ * f y) = 1 at hh
        symm
        simpa only [map_mul, map_inv, inv_mul_eq_one] using hh
      · simp only [map_one]
      · intro y z _ _ hy hz
        simp only [map_mul, hy, hz]
      · intro y _ hy
        simp only [map_inv, hy]
    apply (QuotientGroup.eq_one_iff (N := commutator G) _).mp
    change q (x⁻¹ * f x) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel]

end MonoidHom
