module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
/-!
# Smooth entries of a nonsingular matrix inverse

An entrywise smooth family of real square matrices has entrywise smooth
inverse wherever its determinant is nonzero. The parameter space is any real
normed space and the differentiability order is arbitrary. No openness
hypothesis is required because smoothness is taken within the given set.

Expand determinant as a finite sum of products. Each adjugate entry is the
determinant of a matrix with one constant row. The adjugate formula then
reduces matrix inversion to smooth scalar reciprocal and multiplication.
This supplies inverse metric coefficients for coordinate curvature calculus.
Source: the standard adjugate formula, as formalized in Mathlib; the entrywise
proof route is also used in the local differential-geometry project.
-/

open Set
open scoped ContDiff BigOperators
noncomputable section
namespace Matrix
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {n : Type*} [Fintype n] [DecidableEq n] {r : ℕ∞ω}
  {s : Set X} {A : X → Matrix n n ℝ}
private theorem det_contDiffOn_of_entries
    (hA : ∀ i j, ContDiffOn ℝ r (fun p => A p i j) s) :
    ContDiffOn ℝ r (fun p => (A p).det) s := by
  classical
  simp_rw [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => ?_
  exact contDiffOn_const.mul (contDiffOn_prod fun i _ => hA (σ i) i)
private theorem adjugate_contDiffOn_of_entries
    (hA : ∀ i j, ContDiffOn ℝ r (fun p => A p i j) s) (a b : n) :
    ContDiffOn ℝ r (fun p => (A p).adjugate a b) s := by
  classical
  simp_rw [Matrix.adjugate_apply]
  refine det_contDiffOn_of_entries (A := fun p => (A p).updateRow b (Pi.single a 1)) ?_
  intro i j
  by_cases hij : i = b
  · subst hij
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simpa only [Matrix.updateRow_ne hij] using hA i j
/-- Smooth matrix entries and a nonvanishing determinant give smooth inverse entries. -/
public theorem contDiffOn_inv_entry
    (hA : ∀ i j, ContDiffOn ℝ r (fun p => A p i j) s)
    (hdet : ∀ p ∈ s, (A p).det ≠ 0) (a b : n) :
    ContDiffOn ℝ r (fun p => (A p)⁻¹ a b) s := by
  classical
  have hrewrite : (fun p => (A p)⁻¹ a b) =
      fun p => (A p).det⁻¹ * (A p).adjugate a b := by
    funext p
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hrewrite]
  exact ((det_contDiffOn_of_entries hA).inv hdet).mul
    (adjugate_contDiffOn_of_entries hA a b)
end Matrix
