module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Group

/-!
# Automorphisms preserving a root with central square

If t has central square, conjugation by t and by its inverse agree. Therefore
an automorphism sending t to t or its inverse commutes with that conjugation.
No condition on the order of the automorphism is needed.

This elementary observation is used in the semilinear normalization of the
Ree residual extension (Thompson VI, pp.629–630; Parrott 1972, pp.672–674).
-/

namespace MulAut
open Subgroup
variable {K : Type*} [Group K]

public theorem conj_inv_eq_of_square_central (t : K) (ht : t ^ 2 ∈ center K) :
    MulAut.conj (t⁻¹) = MulAut.conj t := by
  have hh : MulAut.conj (t ^ 2) = 1 := by
    ext x
    change t ^ 2 * x * (t ^ 2)⁻¹ = x
    rw [← (mem_center_iff.mp ht x), mul_inv_cancel_right]
  rw [map_pow, pow_two] at hh
  rw [map_inv]
  exact inv_eq_of_mul_eq_one_right hh

/-- A symmetry preserving or inverting a root with central square commutes with
its inner automorphism. In particular, an order-four lift is unnecessary. -/
public theorem commute_conj_of_preserves_root (σ : MulAut K) (t : K)
    (ht : t ^ 2 ∈ center K) (hσ : σ t = t ∨ σ t = t⁻¹) :
    Commute σ (MulAut.conj t) := by
  have hinv := conj_inv_eq_of_square_central t ht
  ext x
  change σ (t * x * t⁻¹) = t * σ x * t⁻¹
  rw [map_mul, map_mul, map_inv]
  rcases hσ with h | h
  · rw [h]
  · rw [h]
    exact congrArg (fun f : MulAut K => f (σ x)) hinv

end MulAut
