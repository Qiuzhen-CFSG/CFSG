/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/EisensteinSpan.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.Eisenstein
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Integral and Eisenstein spans

Closure under multiplication by omega transfers the Eisenstein span into an integral submodule.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/EisensteinSpan.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Algebra
open scoped QuadraticAlgebra

/-- The integral coordinates of an Eisenstein scalar in the basis 1, omega. -/
theorem eisenstein_eq_re_add_im_omega (a : Eisenstein) :
    a = (a.re : Eisenstein) + (a.im : Eisenstein) * eisensteinOmega := by
  ext <;> simp [eisensteinOmega, QuadraticAlgebra.omega]

/-- Containing a vector and its omega multiple suffices for an integral
submodule to contain all Eisenstein multiples of that vector. -/
theorem eisenstein_smul_mem_of_mem_omega
    {M : Type*} [AddCommGroup M] [Module Eisenstein M] [Module ℤ M]
    (S : Submodule ℤ M) {v : M} (hv : v ∈ S) (hω : eisensteinOmega • v ∈ S)
    (a : Eisenstein) : a • v ∈ S := by
  rw [eisenstein_eq_re_add_im_omega a, add_smul, mul_smul,
    Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact S.add_mem (S.toAddSubgroup.zsmul_mem hv a.re)
    (S.toAddSubgroup.zsmul_mem hω a.im)

/-- Restriction from Eisenstein span to integral span requires each generator
and its omega multiple, with no comparison of ranks or determinants. -/
theorem eisensteinSpan_subset_intSubmodule
    {M : Type*} [AddCommGroup M] [Module Eisenstein M] [Module ℤ M]
    (G : Set M) (S : Submodule ℤ M)
    (hg : ∀ g ∈ G, g ∈ S) (hω : ∀ g ∈ G, eisensteinOmega • g ∈ S) :
    ∀ v ∈ Submodule.span Eisenstein G, v ∈ S := by
  let T : Submodule Eisenstein M :=
    { carrier := {v | ∀ a : Eisenstein, a • v ∈ S}
      zero_mem' := by intro a; simp
      add_mem' := by
        intro x y hx hy a
        simpa only [smul_add] using S.add_mem (hx a) (hy a)
      smul_mem' := by
        intro a x hx b
        simpa only [mul_smul] using hx (b * a) }
  have hGT : G ⊆ T := by
    intro g hgG a
    exact eisenstein_smul_mem_of_mem_omega S (hg g hgG) (hω g hgG) a
  have hspan : Submodule.span Eisenstein G ≤ T := Submodule.span_le.mpr hGT
  intro v hv
  have h := hspan hv (1 : Eisenstein)
  simpa using h

end Atlas.Algebra
