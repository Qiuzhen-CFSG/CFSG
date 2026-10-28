/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/EisensteinApproximation.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.EisensteinRational
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Approximation by Eisenstein integers

A rational Eisenstein scalar is within squared norm one-half of an integral scalar. The proof bounds the distance to corners of a fundamental triangle.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/EisensteinApproximation.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.Algebra
open scoped QuadraticAlgebra

private theorem eisenstein_triangle_near (r s : ℚ)
    (hr : r ≤ 1) (hs : 0 ≤ s) (hsr : s ≤ r) :
    r^2-r*s+s^2 ≤ 1/2 ∨
      (r-1)^2-(r-1)*s+s^2 ≤ 1/2 ∨
      (r-1)^2-(r-1)*(s-1)+(s-1)^2 ≤ 1/2 := by
  by_contra! h
  have h0 := mul_nonneg (show 0 ≤ 1-r by linarith)
    (show 0 ≤ r^2-r*s+s^2-1/2 by linarith [h.1])
  have h1 := mul_nonneg (show 0 ≤ r-s by linarith)
    (show 0 ≤ (r-1)^2-(r-1)*s+s^2-1/2 by linarith [h.2.1])
  have h2 := mul_nonneg hs
    (show 0 ≤ (r-1)^2-(r-1)*(s-1)+(s-1)^2-1/2 by linarith [h.2.2])
  nlinarith [sq_nonneg (2*r-s-1), sq_nonneg (s-1/3)]

/-- One corner of each unit parallelogram is within squared Eisenstein norm one-half. -/
theorem eisenstein_near_corner (r s : ℚ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    r^2-r*s+s^2 ≤ 1/2 ∨
      (r-1)^2-(r-1)*s+s^2 ≤ 1/2 ∨
      r^2-r*(s-1)+(s-1)^2 ≤ 1/2 ∨
      (r-1)^2-(r-1)*(s-1)+(s-1)^2 ≤ 1/2 := by
  by_cases h : s ≤ r
  · rcases eisenstein_triangle_near r s hr1 hs0 h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · have h' : r ≤ s := le_of_lt (lt_of_not_ge h)
    rcases eisenstein_triangle_near s r hs1 hr0 h' with h | h | h
    · exact Or.inl (by nlinarith)
    · exact Or.inr (Or.inr (Or.inl (by nlinarith)))
    · exact Or.inr (Or.inr (Or.inr (by nlinarith)))

/-- Every rational Eisenstein scalar is within squared norm one-half of an
integral Eisenstein scalar. This elementary lattice approximation uses the
three corners of one equilateral triangle; no Euclidean-domain instance or
lattice uniqueness theorem is assumed. -/
theorem eisenstein_rational_approximation (c : EisensteinRational) :
    ∃ a : Eisenstein, (c - eisensteinToRational a).norm ≤ 1/2 := by
  let n := Int.floor c.re
  let m := Int.floor c.im
  let r : ℚ := c.re - n
  let s : ℚ := c.im - m
  have hr0 : 0 ≤ r := sub_nonneg.mpr (Int.floor_le c.re)
  have hr1 : r ≤ 1 := (Int.fract_lt_one c.re).le
  have hs0 : 0 ≤ s := sub_nonneg.mpr (Int.floor_le c.im)
  have hs1 : s ≤ 1 := (Int.fract_lt_one c.im).le
  rcases eisenstein_near_corner r s hr0 hr1 hs0 hs1 with h | h | h | h
  · refine ⟨⟨n,m⟩, ?_⟩
    dsimp only [r, s] at h
    simp [QuadraticAlgebra.norm_def, eisensteinToRational]
    nlinarith [h]
  · refine ⟨⟨n+1,m⟩, ?_⟩
    dsimp only [r, s] at h
    simp [QuadraticAlgebra.norm_def, eisensteinToRational]
    nlinarith [h]
  · refine ⟨⟨n,m+1⟩, ?_⟩
    dsimp only [r, s] at h
    simp [QuadraticAlgebra.norm_def, eisensteinToRational]
    nlinarith [h]
  · refine ⟨⟨n+1,m+1⟩, ?_⟩
    dsimp only [r, s] at h
    simp [QuadraticAlgebra.norm_def, eisensteinToRational]
    nlinarith [h]

end Atlas.Algebra
