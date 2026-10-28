module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Test matrices for a Sylow-fixed standard action on PSL₃

For a unit of order four, the two displayed diagonal matrices generate a
copy of C₄ × C₄. The determinant-one coordinate interchange normalizes that
torus. Their projective images are the tests for the pointwise fixer calculation;
this module defines the matrices without asserting the two-subgroup containment.
The possible remaining conjugations are parametrized by `diag(1,1,t)`, and
their image is cyclic over a finite field.

Source: the matrix actions in GLS3, §2.7,
`refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115, for the linear alternatives
of Aschbacher–Smith F.6.18(10)–(11), printed pp.309–310, used in 15.4.18,
printed pp.1162–1163. The quotient is always the actual SL₃ scalar quotient.
-/

@[expose] public section

open scoped MatrixGroups
namespace Matrix.PSL3.SylowFixedActions.Standard
open Matrix.PSL3.OuterSolvable
variable (F : Type*) [Field F]

/-- The determinant-one diagonal torus, in explicit coordinates. -/
def diagonalSL : (Fˣ × Fˣ) →* SL(3, F) where
  toFun u := ⟨Matrix.diagonal ![(u.1 : F), (u.2 : F), ((u.1 * u.2)⁻¹ : Fˣ)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, ← mul_assoc]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  map_mul' u v := by
    apply Subtype.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

@[simp] theorem diagonalSL_val (u : Fˣ × Fˣ) :
    (diagonalSL F u).val =
      Matrix.diagonal ![(u.1 : F), (u.2 : F), ((u.1 * u.2)⁻¹ : Fˣ)] := rfl

def testDiagonal₁ (u : Fˣ) : SL(3, F) := diagonalSL F (u, u⁻¹)
def testDiagonal₂ (u : Fˣ) : SL(3, F) := diagonalSL F (1, u)

/-- Interchange the first two coordinates and negate the last coordinate. -/
def interchange : SL(3, F) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

theorem interchange_sq : interchange F ^ 2 = 1 := by
  apply Subtype.ext
  change (!![0, 1, 0; 1, 0, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) F) ^ 2 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three]

/-- The three projective matrices used to test pointwise fixation. -/
def testSet (u : Fˣ) : Set PSL(3, F) :=
  {projection F (testDiagonal₁ F u), projection F (testDiagonal₂ F u),
    projection F (interchange F)}

/-- The remaining diagonal conjugations, parametrized by one field unit. -/
def fixerMatrix : Fˣ →* GL (Fin 3) F where
  toFun u := {
    val := Matrix.diagonal ![1, 1, (u : F)]
    inv := Matrix.diagonal ![1, 1, (u⁻¹ : Fˣ)]
    val_inv := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
    inv_val := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] }
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  map_mul' u v := by
    apply Units.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp

def fixerAction : Fˣ →* MulAut PSL(3, F) :=
  (linearConj F).comp (fixerMatrix F)

theorem fixerAction_range_isCyclic [Finite F] : IsCyclic (fixerAction F).range :=
  isCyclic_of_surjective (fixerAction F).rangeRestrict
    (fixerAction F).rangeRestrict_surjective

theorem testDiagonal₁_pow_four (u : Fˣ) (hu : u ^ 4 = 1) :
    testDiagonal₁ F u ^ 4 = 1 := by
  rw [testDiagonal₁, ← map_pow]
  have h : (u, u⁻¹) ^ 4 = (1 : Fˣ × Fˣ) := by
    apply Prod.ext
    · exact hu
    · change u⁻¹ ^ 4 = 1
      rw [inv_pow, hu, inv_one]
  rw [h, map_one]

theorem testDiagonal₂_pow_four (u : Fˣ) (hu : u ^ 4 = 1) :
    testDiagonal₂ F u ^ 4 = 1 := by
  rw [testDiagonal₂, ← map_pow]
  have h : ((1 : Fˣ), u) ^ 4 = (1 : Fˣ × Fˣ) := by ext <;> simp [hu]
  rw [h, map_one]

end Matrix.PSL3.SylowFixedActions.Standard
