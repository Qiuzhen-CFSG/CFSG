/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.Ring

/-!
# Split and odd quadratic spaces

Adapted from `Atlas/LinearGroups/Orthogonal/Basic.lean`: only the coordinate
forms and polarization formulas are retained, under a CFSG namespace and
narrow imports. These are the hyperbolic coordinates of GLS3 §2.7.
The odd space has one extra square coordinate; in characteristic two its
polar radical is that coordinate line, although the quadratic space is regular.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal

abbrev Index (n : ℕ) := Fin n ⊕ Fin n
abbrev VectorD (n : ℕ) (F : Type*) := Index n → F
abbrev VectorB (n : ℕ) (F : Type*) := VectorD n F × F

variable {n : ℕ} {F : Type*} [CommRing F]

/-- The split quadratic form on the ordered hyperbolic coordinates. -/
def formD (n : ℕ) (F : Type*) [CommRing F] : QuadraticForm F (VectorD n F) :=
  ∑ i : Fin n, QuadraticMap.proj (R := F) (.inl i) (.inr i)

/-- The odd-dimensional quadratic form, including its anisotropic last coordinate. -/
def formB (n : ℕ) (F : Type*) [CommRing F] : QuadraticForm F (VectorB n F) :=
  (formD n F).comp (LinearMap.fst F _ _) +
    (QuadraticMap.sq (R := F)).comp (LinearMap.snd F _ _)

@[simp] theorem formD_apply (v : VectorD n F) :
    formD n F v = ∑ i : Fin n, v (.inl i) * v (.inr i) := by
  simp [formD, QuadraticMap.proj, QuadraticMap.linMulLin_apply]

@[simp] theorem formB_apply (v : VectorB n F) :
    formB n F v = formD n F v.1 + v.2 ^ 2 := by
  simp [formB, QuadraticMap.sq, QuadraticMap.linMulLin_apply, pow_two]

/-- Polarization of the split form is nondegenerate even in characteristic two. -/
theorem polarD_apply (u v : VectorD n F) :
    (formD n F).polarBilin u v =
      ∑ i : Fin n, (u (.inl i) * v (.inr i) + v (.inl i) * u (.inr i)) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, formD_apply, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem polarB_apply (u v : VectorB n F) :
    (formB n F).polarBilin u v = (formD n F).polarBilin u.1 v.1 + 2 * u.2 * v.2 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, formB_apply,
    Prod.fst_add, Prod.snd_add]
  ring

end ClassicalOrthogonal
