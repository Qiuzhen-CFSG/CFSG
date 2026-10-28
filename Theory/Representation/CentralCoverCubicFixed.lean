module
public import Theory.Representation.FirstCohomologyDuality

/-!
# Cubic fixed vectors in a central binary cover

A cubic actor that fixes the image of a vector in a central binary cover
fixes that vector itself. Its displacement lies in the fixed kernel, so
its square fixes the vector; coprimality with three finishes the argument.
This is the covering step in Aschbacher–Smith13.7.6(5), printed p.939.
-/

open Representation
public section
namespace Representation.OneCohomology
variable {A U W : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- A cubic fixes every lift of each fixed quotient vector in a central cover. -/
theorem cubic_fixed_of_central_cover
    (ρ : Representation (ZMod 2) A U) (σ : Representation (ZMod 2) A W)
    (p : ρ.IntertwiningMap σ)
    (hk : ∀ u, p u = 0 → ∀ a, ρ a u = u)
    (a : A) (ha : a ^ 3 = 1) (u : U) (hu : σ a (p u) = p u) :
    ρ a u = u := by
  have htwo (v : U) : v + v = 0 := by
    calc
      v + v = (1 + 1 : ZMod 2) • v := by rw [add_smul, one_smul]
      _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 by decide, zero_smul]
  have hneg (v : U) : -v = v := neg_eq_iff_add_eq_zero.mpr (htwo v)
  have hd : ρ a (ρ a u - u) = ρ a u - u := by
    apply hk
    have he : p (ρ a u) = σ a (p u) := LinearMap.congr_fun (p.isIntertwining' a) u
    rw [map_sub, he, hu, sub_self]
  have hsq : ρ a (ρ a u) = u := by
    calc
      ρ a (ρ a u) = (ρ a (ρ a u) - ρ a u) + ρ a u := (sub_add_cancel _ _).symm
      _ = (ρ a u - u) + ρ a u := by rw [← map_sub, hd]
      _ = (ρ a u + ρ a u) - u := by abel
      _ = u := by rw [htwo, zero_sub, hneg]
  have hc := LinearMap.congr_fun (congrArg ρ ha) u
  simp only [pow_succ, pow_zero, map_mul, map_one,
    Module.End.mul_apply, Module.End.one_apply] at hc
  simpa only [hsq] using hc
end Representation.OneCohomology
