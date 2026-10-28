module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorOrthogonal

/-!
Adapted from `Atlas/LinearGroups/Orthogonal/B2ExteriorKernel.lean`.
The three-row minor identity forces a matrix acting trivially on its exterior
square to be scalar. Only this field-independent kernel argument is retained.
-/

@[expose] public noncomputable section
namespace Atlas.Order20160A8.Bivectors
open Matrix
variable {F : Type} [Field F]

/-- Every ordered minor can be recovered from the six exterior coordinates. -/
theorem wedge_eq_minor {u v x y : Four F} (h : wedge u v = wedge x y) (i j : Fin 4) :
    u i * v j - u j * v i = x i * y j - x j * y i := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  simp [wedge] at h0 h1 h2 h3 h4 h5
  have hn0 : u 1 * v 0 - u 0 * v 1 = x 1 * y 0 - x 0 * y 1 := by
    linear_combination -h0
  have hn1 : u 2 * v 0 - u 0 * v 2 = x 2 * y 0 - x 0 * y 2 := by
    linear_combination -h1
  have hn2 : u 3 * v 0 - u 0 * v 3 = x 3 * y 0 - x 0 * y 3 := by
    linear_combination -h2
  have hn3 : u 2 * v 1 - u 1 * v 2 = x 2 * y 1 - x 1 * y 2 := by
    linear_combination -h3
  have hn4 : u 3 * v 1 - u 1 * v 3 = x 3 * y 1 - x 1 * y 3 := by
    linear_combination -h4
  have hn5 : u 3 * v 2 - u 2 * v 3 = x 3 * y 2 - x 2 * y 3 := by
    linear_combination -h5
  fin_cases i <;> fin_cases j <;> first | assumption | simp

/-- An identity exterior square forces the original four-dimensional matrix to be scalar. -/
theorem scalar_of_exteriorMap_eq_id (A : Matrix (Fin 4) (Fin 4) F)
    (hA : ∀ w, exteriorMap A w = w) : ∃ c : F, c ^ 2 = 1 ∧ A = c • 1 := by
  have hm (i j a b : Fin 4) : A i a * A j b - A j a * A i b =
      ((Pi.single a (1 : F)) : Four F) i * ((Pi.single b (1 : F)) : Four F) j -
      ((Pi.single a (1 : F)) : Four F) j * ((Pi.single b (1 : F)) : Four F) i := by
    have h := hA (wedge (Pi.single a (1 : F)) (Pi.single b (1 : F)))
    rw [exteriorMap_wedge] at h
    simpa using wedge_eq_minor h i j
  have ho (k i : Fin 4) (hki : k ≠ i) : A k i = 0 := by
    obtain ⟨j, hji, hjk⟩ : ∃ j : Fin 4, j ≠ i ∧ j ≠ k := by
      fin_cases k <;> fin_cases i <;> first | contradiction | decide
    have h1 := hm i j i j
    have h2 := hm i k i j
    have h3 := hm j k i j
    simp [hji, hki, Ne.symm hji, Ne.symm hjk] at h1 h2 h3
    linear_combination -A k i * h1 + A j i * h2 - A i i * h3
  have hd (i j : Fin 4) (hij : i ≠ j) : A i i * A j j = 1 := by
    have h := hm i j i j
    simpa [hij, Ne.symm hij, ho i j hij, ho j i (Ne.symm hij)] using h
  have ha : A 0 0 ≠ 0 := by
    intro h
    have hh := hd 0 1 (by decide)
    simp [h] at hh
  have h01 := hd 0 1 (by decide)
  have h02 := hd 0 2 (by decide)
  have h12 := hd 1 2 (by decide)
  have hs : A 0 0 ^ 2 = 1 := by
    linear_combination -A 0 0 * A 0 0 * h12 + A 0 0 * A 2 2 * h01 + h02
  refine ⟨A 0 0, hs, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    by_cases hi : i = 0
    · subst i; rfl
    apply mul_left_cancel₀ ha
    have hh := hd 0 i (Ne.symm hi)
    linear_combination hh - hs
  · simp [hij, ho i j hij]


end Atlas.Order20160A8.Bivectors
