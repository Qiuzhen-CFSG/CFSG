/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/RankOneTrace.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum

/-!
# Rank-one perturbation traces

The square of a rank-one endomorphism reduces to a scalar multiple.
Linearity of trace computes the square of a scalar rank-one perturbation,
including the dimension-783 value needed in the root criterion.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/RankOneTrace.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Remove a simplification argument unused by this toolchain.
Definitions remain exposed for the source computational interfaces.
-/

@[expose] public section

namespace Atlas.Algebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The square of an actual rank-one endomorphism, with no spectral hypothesis. -/
theorem rankOne_smulRight_square (f : V →ₗ[K] K) (x : V) :
    (f.smulRight x : Module.End K V) ^ 2 = f x • f.smulRight x := by
  ext y
  simp [pow_two, Module.End.mul_apply, LinearMap.smulRight_apply, smul_smul]
  congr 1
  ring

/-- Trace of a scalar rank-one perturbation squared. -/
theorem trace_one_add_rankOne_square [FiniteDimensional K V]
    (f : V →ₗ[K] K) (x : V) (a : K) :
    LinearMap.trace K V ((1 + a • f.smulRight x : Module.End K V) ^ 2) =
      (Module.finrank K V : K) + (2 * a + a ^ 2 * f x) * f x := by
  have he : (1 + a • f.smulRight x : Module.End K V) ^ 2 =
      1 + (2 * a + a ^ 2 * f x) • f.smulRight x := by
    ext y
    simp only [pow_two, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, map_add, map_smul,
      smul_add, smul_smul]
    module
  rw [he, map_add, map_smul, LinearMap.trace_one, LinearMap.trace_smulRight, smul_eq_mul]

/-- The numerical trace used in the cubic root criterion, derived from rank one. -/
theorem trace_one_add_eleven_rankOne_square [CharZero K] [FiniteDimensional K V]
    (f : V →ₗ[K] K) (x : V) (hx : f x = 9) (hd : Module.finrank K V = 783) :
    LinearMap.trace K V ((1 + (11 : K) • f.smulRight x : Module.End K V) ^ 2) = 10782 := by
  rw [trace_one_add_rankOne_square, hx, hd]
  norm_num

end Atlas.Algebra
