module

public import Theory.Representation.PSL3Two.SmallModules
import Mathlib.Tactic.FinCases

/-!
# Coordinates for the binary adjoint module

The trace-zero endomorphisms of the natural three-space have eight coordinates:
the six off-diagonal entries and two diagonal entries. The remaining diagonal
entry is their sum over F₂. Conjugation by a coordinate cycle and an elementary
transvection is computed in this basis. These identities connect finite matrix
certificates to the actual representation, rather than an unrelated matrix model.

Source: Aschbacher–Smith H.6.1–2, printed pp.386–387, combined manuscript
of 1 March 2004. This module supplies coordinates, not an irreducible catalogue.
-/

@[expose] public section

open Matrix Representation
namespace BinaryLinearThree.IrreducibleCatalogue

abbrev Eight := Fin 8 → ZMod 2

def matrixOf (v : Eight) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![v 6, v 0, v 1; v 2, v 7, v 3; v 4, v 5, v 6 + v 7]

def readMatrix (a : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Eight :=
  ![a 0 1, a 0 2, a 1 0, a 1 2, a 2 0, a 2 1, a 0 0, a 1 1]

private theorem matrixOf_trace (v : Eight) : (matrixOf v).trace = 0 := by
  simp [matrixOf, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private theorem matrixOf_readMatrix (a : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (ha : a.trace = 0) : matrixOf (readMatrix a) = a := by
  have hdiag : a 0 0 + a 1 1 = a 2 2 := by
    have he : a 0 0 + a 1 1 + a 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_three] using ha
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using
      congrArg (fun x => x + a 2 2) he
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixOf, readMatrix, hdiag]

noncomputable def coordinates : Steinberg ≃ₗ[ZMod 2] Eight where
  toFun f := readMatrix (LinearMap.toMatrix' f.val)
  invFun v := ⟨(matrixOf v).toLin', by
    change (LinearMap.trace (ZMod 2) Vector) (matrixOf v).toLin' = 0
    rw [Matrix.trace_toLin'_eq]
    exact matrixOf_trace v⟩
  left_inv f := by
    apply Subtype.ext
    change (matrixOf (readMatrix (LinearMap.toMatrix' f.val))).toLin' = f.val
    rw [matrixOf_readMatrix, Matrix.toLin'_toMatrix']
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    exact f.property
  right_inv v := by
    change readMatrix (LinearMap.toMatrix' (matrixOf v).toLin') = v
    rw [LinearMap.toMatrix'_toLin']
    funext i
    fin_cases i <;> rfl
  map_add' f h := by
    change readMatrix (LinearMap.toMatrix' (f.val + h.val)) = _
    rw [map_add]
    funext i
    fin_cases i <;> rfl
  map_smul' c f := by
    change readMatrix (LinearMap.toMatrix' (c • f.val)) = _
    rw [map_smul]
    funext i
    fin_cases i <;> rfl

def cycle : Group := ⟨!![0,0,1;1,0,0;0,1,0], by decide⟩
def shear : Group := ⟨!![1,1,0;0,1,0;0,0,1], by decide⟩

def cycleMatrix : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,1,0,0,0,0,0,0;
     1,0,0,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,0,0,0,1,1;
     0,0,0,0,0,0,1,0]

def shearMatrix : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1,0,1,0,0,0,1,1;
     0,1,0,1,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,1,1,0,0;
     0,0,1,0,0,0,1,0;
     0,0,1,0,0,0,0,1]

noncomputable def coordinateMatrix (g : Group) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  LinearMap.toMatrix' (coordinates.conj (S g))

theorem coordinateMatrix_cycle : coordinateMatrix cycle = cycleMatrix := by
  have hi : cycle⁻¹ = cycle * cycle := by
    apply inv_eq_of_mul_eq_one_right
    decide
  ext i j
  change readMatrix (LinearMap.toMatrix'
    (W cycle ∘ₗ (matrixOf (Pi.single j 1)).toLin' ∘ₗ W cycle⁻¹)) i = _
  rw [hi]
  fin_cases i <;> fin_cases j <;> decide

theorem coordinateMatrix_shear : coordinateMatrix shear = shearMatrix := by
  have hi : shear⁻¹ = shear := by
    apply inv_eq_of_mul_eq_one_right
    decide
  ext i j
  change readMatrix (LinearMap.toMatrix'
    (W shear ∘ₗ (matrixOf (Pi.single j 1)).toLin' ∘ₗ W shear⁻¹)) i = _
  rw [hi]
  fin_cases i <;> fin_cases j <;> decide

end BinaryLinearThree.IrreducibleCatalogue
