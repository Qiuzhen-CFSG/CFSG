module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Coordinates
import Mathlib.Tactic.FinCases
/-!
# Six positive roots and their torus in the marked SU₄(3) coordinates

The roots are A(1), A(i), B(i), C(1), C(i), D(i), with i² = -1.
Here A(a) has entries a in position (0,1) and -bar(a) in (2,3);
C(c) has entries c in (0,2) and -bar(c) in (1,3); B and D are the
trace-zero long roots in positions (1,2) and (0,3). Each matrix is
special unitary for the published antidiagonal form and has cube one.
Two diagonal special unitary matrices invert the short and long roots,
respectively. Projection throughout is the original coordinateProjection.

These are the concrete inputs to the cubic-lifting calculation for
Aschbacher--Smith I.1.4(5), printed p.408, and GLS3 §6.1. The four
collection tails fix the conventions for the separate presentation proof.
No assertion that the whole positive subgroup has exponent three is used.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourThree.IsotropicStabilizers
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary
namespace RootLifts
abbrev K := FiniteField.Nine
abbrev Mat := Matrix (Fin 4) (Fin 4) K
def imaginary : K := ⟨0, 1⟩
def rootMatrix : Fin 6 → Mat
  | 0 => !![1,1,0,0; 0,1,0,0; 0,0,1,-1; 0,0,0,1]
  | 1 => !![1,imaginary,0,0; 0,1,0,0; 0,0,1,imaginary; 0,0,0,1]
  | 2 => !![1,0,0,0; 0,1,imaginary,0; 0,0,1,0; 0,0,0,1]
  | 3 => !![1,0,1,0; 0,1,0,-1; 0,0,1,0; 0,0,0,1]
  | 4 => !![1,0,imaginary,0; 0,1,0,imaginary; 0,0,1,0; 0,0,0,1]
  | 5 => !![1,0,0,imaginary; 0,1,0,0; 0,0,1,0; 0,0,0,1]
theorem rootMatrix_cube (r : Fin 6) : rootMatrix r ^ 3 = 1 := by
  fin_cases r <;> decide +kernel

def rootGL (r : Fin 6) : GL (Fin 4) K :=
  ⟨rootMatrix r, rootMatrix r ^ 2,
    by rw [← pow_succ', rootMatrix_cube], by rw [← pow_succ, rootMatrix_cube]⟩
theorem rootGL_special (r : Fin 6) : rootGL r ∈ coordinateForm.specialSubgroup := by
  rw [coordinateForm.mem_specialSubgroup_iff]
  constructor
  · change coordinateForm.conjTranspose (rootMatrix r) * coordinateForm.form * rootMatrix r = _
    fin_cases r <;> decide +kernel
  · apply Units.ext
    change (rootMatrix r).det = 1
    fin_cases r <;> decide +kernel

def rootSU (r : Fin 6) : CoordinateSU := ⟨rootGL r, rootGL_special r⟩
theorem rootSU_mem (r : Fin 6) : rootSU r ∈ positiveSU := by
  apply Subgroup.subset_closure
  change (∀ i j : Fin 4, j < i → rootMatrix r i j = 0) ∧
    ∀ i : Fin 4, rootMatrix r i i = 1
  constructor
  · intro i j hij
    fin_cases r <;> fin_cases i <;> fin_cases j <;>
      norm_num [rootMatrix] at *
  · intro i
    fin_cases r <;> fin_cases i <;> rfl

def torusMatrix : Fin 2 → Mat
  | 0 => Matrix.diagonal ![1,-1,-1,1]
  | 1 => Matrix.diagonal ![1+imaginary,-1+imaginary,1-imaginary,-1-imaginary]
def torusInverse : Fin 2 → Mat
  | 0 => torusMatrix 0
  | 1 => Matrix.diagonal ![-1+imaginary,1+imaginary,-1-imaginary,1-imaginary]

def torusGL (r : Fin 2) : GL (Fin 4) K :=
  ⟨torusMatrix r, torusInverse r,
    by fin_cases r <;> decide +kernel, by fin_cases r <;> decide +kernel⟩
theorem torusGL_special (r : Fin 2) : torusGL r ∈ coordinateForm.specialSubgroup := by
  rw [coordinateForm.mem_specialSubgroup_iff]
  constructor
  · change coordinateForm.conjTranspose (torusMatrix r) * coordinateForm.form * torusMatrix r = _
    fin_cases r <;> decide +kernel
  · apply Units.ext
    change (torusMatrix r).det = 1
    fin_cases r <;> decide +kernel

def torusSU (r : Fin 2) : CoordinateSU := ⟨torusGL r, torusGL_special r⟩
def inverterIndex (r : Fin 6) : Fin 2 := if r = 2 ∨ r = 5 then 1 else 0

theorem rootSU_cube (r : Fin 6) : rootSU r ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact rootMatrix_cube r

theorem torusSU_inverts (r : Fin 6) :
    torusSU (inverterIndex r) * rootSU r * (torusSU (inverterIndex r))⁻¹ =
      (rootSU r)⁻¹ := by
  have h : torusSU (inverterIndex r) * rootSU r =
      rootSU r ^ 2 * torusSU (inverterIndex r) := by
    apply Subtype.ext
    apply Units.ext
    change torusMatrix (inverterIndex r) * rootMatrix r =
      rootMatrix r ^ 2 * torusMatrix (inverterIndex r)
    fin_cases r <;> decide +kernel
  rw [h, mul_inv_cancel_right]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, rootSU_cube]

def root (r : Fin 6) : S := coordinateProjection (rootSU r)
def torus (r : Fin 2) : S := coordinateProjection (torusSU r)
theorem root_cube (r : Fin 6) : root r ^ 3 = 1 := by
  rw [root, ← map_pow, rootSU_cube, map_one]
theorem torus_inverts (r : Fin 6) :
    torus (inverterIndex r) * root r * (torus (inverterIndex r))⁻¹ = (root r)⁻¹ := by
  simpa only [root, torus, map_mul, map_inv] using congrArg coordinateProjection (torusSU_inverts r)
theorem root_mem_positive (r : Fin 6) : root r ∈ positive :=
  ⟨rootSU r, rootSU_mem r, rfl⟩
/-- The four nontrivial tails in descending collection order. -/
def swapTail {H : Type*} [Monoid H] (x : Fin 6 → H) (i j : Fin 6) : H :=
  if i = 0 ∧ j = 2 then x 4 ^ 2 * x 5
  else if i = 1 ∧ j = 2 then x 3 * x 5
  else if i = 1 ∧ j = 3 then x 5 ^ 2
  else if i = 0 ∧ j = 4 then x 5
  else 1

theorem map_swapTail {H K : Type*} [Monoid H] [Monoid K]
    (f : H →* K) (x : Fin 6 → H) (i j : Fin 6) :
    f (swapTail x i j) = swapTail (fun r => f (x r)) i j := by
  unfold swapTail
  split_ifs <;> simp only [map_mul, map_pow, map_one]


end RootLifts
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary
