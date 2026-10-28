module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorKernel

/-!
# Scalar rigidity of the four-dimensional exterior square

A nonzero scalar action on all six bivectors forces the original matrix to
be scalar; the two scalars are related by squaring. The three-row minor
identity proves the vanishing of off-diagonal entries, after which the
principal minors identify all diagonal entries.

Adapted from `Atlas/LinearGroups/Orthogonal/D3ExteriorKernel.lean` and
`B2ExteriorScalar.lean`. This is the scalar-kernel input to the actual
minus-six/PSU₄ quotient comparison (GLS3 §2.7). It is valid in every
characteristic and does not assert faithfulness in odd characteristic.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open Matrix Atlas.Order20160A8.Bivectors
variable {F : Type} [Field F]

theorem exteriorMap_scalar (c : F) :
    exteriorMap (c • (1 : Matrix (Fin 4) (Fin 4) F)) = c^2 • LinearMap.id := by
  apply exterior_ext
  intro u v
  rw [exteriorMap_wedge]
  ext i
  fin_cases i <;> simp [Matrix.smul_mulVec, wedge, pow_two] <;> ring

theorem scalar_of_exteriorMap_scalar (A : Matrix (Fin 4) (Fin 4) F)
    (c : F) (hc : c ≠ 0) (hA : ∀ w, exteriorMap A w = c • w) :
    ∃ a : F, a ^ 2 = c ∧ A = a • 1 := by
  have hm (i j a b : Fin 4) : A i a * A j b - A j a * A i b =
      c * (((Pi.single a (1 : F)) : Four F) i * ((Pi.single b (1 : F)) : Four F) j -
      ((Pi.single a (1 : F)) : Four F) j * ((Pi.single b (1 : F)) : Four F) i) := by
    have h := hA (wedge (Pi.single a (1 : F)) (Pi.single b (1 : F)))
    rw [exteriorMap_wedge] at h
    have hw : wedge (A *ᵥ Pi.single a 1) (A *ᵥ Pi.single b 1) =
        wedge (c • (Pi.single a 1 : Four F)) (Pi.single b 1) := by
      rw [h]
      ext k
      fin_cases k <;> simp [wedge, Pi.smul_apply, smul_eq_mul] <;> ring
    simpa [Pi.smul_apply, smul_eq_mul, mul_sub, mul_assoc] using wedge_eq_minor hw i j

  have ho (k i : Fin 4) (hki : k ≠ i) : A k i = 0 := by
    obtain ⟨j, hji, hjk⟩ : ∃ j : Fin 4, j ≠ i ∧ j ≠ k := by
      fin_cases k <;> fin_cases i <;> first | contradiction | decide
    have h1 := hm i j i j
    have h2 := hm i k i j
    have h3 := hm j k i j
    simp [hji, hki, Ne.symm hji, Ne.symm hjk] at h1 h2 h3
    apply mul_left_cancel₀ hc
    linear_combination -A k i * h1 + A j i * h2 - A i i * h3
  have hd (i j : Fin 4) (hij : i ≠ j) : A i i * A j j = c := by
    have h := hm i j i j
    simpa [hij, Ne.symm hij, ho i j hij, ho j i (Ne.symm hij)] using h
  have ha : A 0 0 ≠ 0 := by
    intro h
    have hh := hd 0 1 (by decide)
    exact hc (by simpa [h] using hh.symm)
  have h01 := hd 0 1 (by decide)
  have h02 := hd 0 2 (by decide)
  have h12 := hd 1 2 (by decide)
  have ha2 : A 2 2 ≠ 0 := by
    intro hz
    exact hc (by simpa [hz] using h02.symm)
  have he01 : A 0 0 = A 1 1 := mul_right_cancel₀ ha2 (h02.trans h12.symm)
  have hs : A 0 0 ^ 2 = c := by
    simpa only [← he01, pow_two] using h01
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

end ClassicalOrthogonal.Minus.OddSixComparison
