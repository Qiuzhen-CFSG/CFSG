/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Forms
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Geometry of the split and odd forms

Adapted from `Atlas/LinearGroups/Orthogonal/Radical.lean`, with imports and
namespaces adapted for CFSG. Testing against hyperbolic coordinate vectors
computes the polar radicals. The square coordinate then proves that the odd
quadratic radical is trivial, including in characteristic two.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal
variable {n : ℕ} {F : Type*} [CommRing F]

def e (i : Fin n) : VectorD n F := Pi.single (.inl i) 1
def f (i : Fin n) : VectorD n F := Pi.single (.inr i) 1
def z : VectorB n F := (0, 1)

@[simp] theorem polarD_e (v : VectorD n F) (i : Fin n) :
    (formD n F).polarBilin v (e i) = v (.inr i) := by
  simp [-QuadraticMap.polarBilin_apply_apply, polarD_apply, e, Pi.single_apply]

@[simp] theorem polarD_f (v : VectorD n F) (i : Fin n) :
    (formD n F).polarBilin v (f i) = v (.inl i) := by
  simp [-QuadraticMap.polarBilin_apply_apply, polarD_apply, f, Pi.single_apply]

theorem polarD_separating (v : VectorD n F)
    (h : ∀ w, (formD n F).polarBilin v w = 0) : v = 0 := by
  funext i
  cases i with
  | inl j => simpa only [polarD_f, Pi.zero_apply] using h (f j)
  | inr j => simpa only [polarD_e, Pi.zero_apply] using h (e j)

theorem polarD_nondegenerate : (formD n F).polarBilin.Nondegenerate := by
  constructor
  · exact polarD_separating
  · intro v h
    apply polarD_separating v
    intro w
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h w

/-- Exact radical description; no division by two or characteristic assumption. -/
theorem polarB_radical_iff (v : VectorB n F) :
    (∀ w, (formB n F).polarBilin v w = 0) ↔ v.1 = 0 ∧ 2 * v.2 = 0 := by
  constructor
  · intro h
    constructor
    · apply polarD_separating
      intro w
      simpa [-QuadraticMap.polarBilin_apply_apply, polarB_apply] using h (w, 0)
    · simpa [-QuadraticMap.polarBilin_apply_apply, polarB_apply, z] using h z
  · rintro ⟨h1,h2⟩ w
    simp [-QuadraticMap.polarBilin_apply_apply, polarB_apply, h1, h2]

@[simp] theorem formB_z : formB n F (z (n := n)) = 1 := by
  simp [-QuadraticMap.polarBilin_apply_apply, z]

/-- In characteristic two the polar radical is exactly the last coordinate line. -/
theorem polarB_radical_charTwo (h2 : (2 : F) = 0) (v : VectorB n F) :
    (∀ w, (formB n F).polarBilin v w = 0) ↔
      ∃ a : F, v = a • z := by
  rw [polarB_radical_iff]
  simp only [h2, zero_mul, and_true]
  constructor
  · intro h
    refine ⟨v.2, ?_⟩
    ext <;> simp [-QuadraticMap.polarBilin_apply_apply, z, h]
  · rintro ⟨a,rfl⟩
    simp [-QuadraticMap.polarBilin_apply_apply, z]

section Field
variable [IsDomain F]

/-- The odd-dimensional form remains quadratically nonsingular in characteristic two. -/
theorem quadratic_radicalB_trivial (v : VectorB n F)
    (hp : ∀ w, (formB n F).polarBilin v w = 0) (hq : formB n F v = 0) : v = 0 := by
  have hv := (polarB_radical_iff v).mp hp
  have hz : v.2 = 0 := by
    have hs : v.2 ^ 2 = 0 := by simpa [-QuadraticMap.polarBilin_apply_apply, hv.1] using hq
    exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hs
  exact Prod.ext hv.1 hz

theorem polarB_separating_of_two_ne_zero (h2 : (2 : F) ≠ 0) (v : VectorB n F)
    (hp : ∀ w, (formB n F).polarBilin v w = 0) : v = 0 := by
  obtain ⟨h1,hz⟩ := (polarB_radical_iff v).mp hp
  exact Prod.ext h1 ((mul_eq_zero.mp hz).resolve_left h2)

end Field
section Dimensions
variable [Nontrivial F]

/-- The split quadratic space has dimension `2n`. -/
theorem vectorD_finrank : Module.finrank F (VectorD n F) = 2 * n := by
  simp [VectorD, Index, Module.finrank_fintype_fun_eq_card, two_mul]

/-- The odd quadratic space has dimension `2n+1`. -/
theorem vectorB_finrank : Module.finrank F (VectorB n F) = 2 * n + 1 := by
  simp [VectorB, VectorD, Index, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card, two_mul]

end Dimensions

@[simp] theorem formD_e (i : Fin n) : formD n F (e i) = 0 := by
  simp [e, Pi.single_apply]

@[simp] theorem formD_f (i : Fin n) : formD n F (f i) = 0 := by
  simp [f, Pi.single_apply]

/-- The coordinate vectors form normalized hyperbolic pairs. -/
@[simp] theorem polarD_ef (i : Fin n) :
    (formD n F).polarBilin (e i) (f i) = 1 := by
  rw [polarD_f]
  simp [e]

/-- In positive rank the split form represents one. -/
theorem formD_e_add_f (i : Fin n) : formD n F (e i + f i) = 1 := by
  rw [QuadraticMap.map_add (formD n F)]
  change formD n F (e i) + formD n F (f i) + (formD n F).polarBilin (e i) (f i) = 1
  rw [formD_e, formD_f, polarD_ef, zero_add, zero_add]

/-- The first coordinate block is a totally singular `n`-space. -/
theorem formD_left_block (x : Fin n → F) : formD n F (Sum.elim x 0) = 0 := by
  simp

end ClassicalOrthogonal
