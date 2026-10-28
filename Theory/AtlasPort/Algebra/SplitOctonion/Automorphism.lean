module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/Algebra/SplitOctonion/Automorphism.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.Algebra.SplitOctonion.Basic
public import Theory.AtlasPort.Algebra.MultiplicativeLinearAutomorphism
public import Mathlib.Tactic.Module
set_option warningAsError false

@[expose] public section

namespace Atlas.SplitOctonion
variable (F : Type*) [Field F]

/-- The full multiplication-preserving linear automorphism group of the concrete algebra. -/
abbrev Automorphism := Atlas.Algebra.multiplicativeLinearAut (R := F) (@mul F _)

variable {F}
@[simp] theorem automorphism_mul (g : Automorphism F) (x y : Carrier F) :
    g.val (mul x y) = mul (g.val x) (g.val y) := g.property x y

@[simp] theorem automorphism_unit (g : Automorphism F) : g.val unit = unit :=
  Atlas.Algebra.MultiplicativeLinearAut.map_unit g unit unit_mul mul_unit

@[simp] theorem automorphism_scalar (g : Automorphism F) (r : F) :
    g.val (r • unit) = r • unit := by rw [map_smul, automorphism_unit]

theorem unit_ne_zero : (unit : Carrier F) ≠ 0 := by
  intro h
  have := congrFun h 3
  simp [unit] at this

/-- Nonscalar elements have unique coefficients relative to the identity. -/
theorem nonscalar_coefficients {x : Carrier F} (hx : ¬ ∃ r : F, x = r • unit)
    {r s : F} (h : r • x = s • unit) : r = 0 ∧ s = 0 := by
  have hr : r = 0 := by
    by_contra hr
    apply hx
    refine ⟨r⁻¹ * s, ?_⟩
    have he := congrArg (fun y : Carrier F => r⁻¹ • y) h
    simpa [smul_smul, inv_mul_cancel₀ hr] using he
  subst r
  have hs := congrFun h 3
  exact ⟨rfl, by simpa [unit] using hs.symm⟩

/-- Trace and norm are forced by multiplication and linearity, in every characteristic. -/
theorem automorphism_trace_norm (g : Automorphism F) (x : Carrier F) :
    trace (g.val x) = trace x ∧ norm (g.val x) = norm x := by
  by_cases hx : ∃ r : F, x = r • unit
  · obtain ⟨r, rfl⟩ := hx
    rw [automorphism_scalar]
    exact ⟨rfl,rfl⟩
  have hgx : ¬ ∃ r : F, g.val x = r • unit := by
    rintro ⟨r, hr⟩
    exact hx ⟨r, g.val.injective (hr.trans (automorphism_scalar g r).symm)⟩
  have h1 := quadratic_identity (g.val x)
  have h2 := congrArg g.val (quadratic_identity x)
  simp only [map_add, map_sub, map_smul, map_zero, automorphism_mul, automorphism_unit] at h2
  have h : (trace (g.val x) - trace x) • g.val x =
      (norm (g.val x) - norm x) • unit := by
    apply sub_eq_zero.mp
    calc
      _ = (mul (g.val x) (g.val x) - trace x • g.val x + norm x • unit) -
          (mul (g.val x) (g.val x) - trace (g.val x) • g.val x + norm (g.val x) • unit) := by module
      _ = 0 := by rw [h1,h2]; simp
  obtain ⟨ht, hn⟩ := nonscalar_coefficients hgx h
  exact ⟨sub_eq_zero.mp ht, sub_eq_zero.mp hn⟩

@[simp] theorem automorphism_trace (g : Automorphism F) (x : Carrier F) :
    trace (g.val x) = trace x := (automorphism_trace_norm g x).1
@[simp] theorem automorphism_norm (g : Automorphism F) (x : Carrier F) :
    norm (g.val x) = norm x := (automorphism_trace_norm g x).2
@[simp] theorem automorphism_conjugate (g : Automorphism F) (x : Carrier F) :
    g.val (conjugate x) = conjugate (g.val x) := by
  simp [conjugate]
end Atlas.SplitOctonion
