/-
Authors: OpenAI
-/

module

public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Huppert II.6.3

Huppert II.6.3 is the definition of a nonidentity transvection over a
hyperplane. The accompanying theorem connects the source convention
`x |-> x - f(x) a` with Mathlib's `LinearEquiv.transvection`.
-/

namespace BenderSuzuki
namespace External

universe u v

/-- Huppert II.6.3: `t` is a nonidentity transvection over the hyperplane `H`. -/
@[expose] public def huppert_II_6_3_isTransvectionOver
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (H : Submodule K V) (t : V ≃ₗ[K] V) : Prop :=
  Module.finrank K (V ⧸ H) = 1 ∧
    t ≠ 1 ∧
    (∀ x : V, x ∈ H → t x = x) ∧
    ∀ x : V, t x - x ∈ H

/-- The source formula `x |-> x - f(x) a` satisfies Huppert II.6.3. -/
public theorem huppert_II_6_3_mathlib_transvection
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (f : Module.Dual K V) (hf : f ≠ 0) (a : V) (ha : a ≠ 0)
    (hfa : f a = 0) :
    huppert_II_6_3_isTransvectionOver f.ker
      (LinearEquiv.transvection (f := f) (v := -a) (by simp [hfa])) := by
  let hneg : f (-a) = 0 := by simp [hfa]
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hquot := Submodule.finrank_quotient_add_finrank f.ker
  have hfinrank : Module.finrank K (V ⧸ f.ker) = 1 := by omega
  have ht_ne : LinearEquiv.transvection hneg ≠ 1 := by
    intro ht
    have hsurj : Function.Surjective f :=
      (LinearMap.range_eq_top).mp (Module.Dual.range_eq_top_of_ne_zero hf)
    obtain ⟨x, hx⟩ := hsurj 1
    have heval := DFunLike.congr_fun ht x
    change x + f x • (-a) = x at heval
    rw [hx] at heval
    simp only [one_smul, add_eq_left] at heval
    exact ha (neg_eq_zero.mp heval)
  refine ⟨hfinrank, ht_ne, ?_, ?_⟩
  · intro x hx
    rw [LinearEquiv.transvection.apply]
    rw [LinearMap.mem_ker.mp hx]
    simp
  · intro x
    rw [LinearEquiv.transvection.apply]
    simp [LinearMap.mem_ker, hfa]

end External
end BenderSuzuki
