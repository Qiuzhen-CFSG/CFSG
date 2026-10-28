module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.Certificate
/-!
# Removing inverses from the seven O'Nan fusion root words

The literal ambient GL words evaluate to B, 1, B, BAB, AB, 1, B.
Expanding their inverses uses the supplied inverse of B and A² = 1,
already certified by `MatrixGenerators.lean`. Associativity gives four
explicit conjugates, shared by the seven root calculations.

The fixed words are recorded in `TreeData.lean` and `Two/source/discovery.json`.
-/

namespace ONan.Simplicity.TwoCertificate.Fusion
private theorem linearRootWord_values (r : Fin 7) :
    linearRootWord r =
      ![linearB, 1, linearB, linearB * linearA * linearB,
        linearA * linearB, 1, linearB] r := by
  fin_cases r <;> simp [linearRootWord, rootWord, ambientWord, mul_assoc]

/-- The four conjugates written with the supplied numerical inverse of B. -/
@[expose] public def inverseFreeConjugate : Fin 7 → Matrix (Fin 45) (Fin 45) (ZMod 7) :=
  let d := matrixB * matrixA * matrixBInv
  let c := matrixA * d * matrixA
  ![d, matrixA, d, matrixB * c * matrixBInv, c, matrixA, d]

/-- Evaluate the actual GL word before doing any numerical multiplication. -/
public theorem root_conjugate (r : Fin 7) :
    (linearRootWord r : Matrix (Fin 45) (Fin 45) (ZMod 7)) * matrixA *
      ((linearRootWord r)⁻¹ : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)) =
        inverseFreeConjugate r := by
  rw [linearRootWord_values]
  fin_cases r
  · change matrixB * matrixA * matrixBInv = matrixB * matrixA * matrixBInv
    rfl
  · change (1 : Matrix (Fin 45) (Fin 45) (ZMod 7)) * matrixA * 1 = matrixA
    simp
  · rfl
  · change (matrixB * matrixA * matrixB) * matrixA *
      (matrixBInv * (matrixA * matrixBInv)) =
        matrixB * (matrixA * (matrixB * matrixA * matrixBInv) * matrixA) * matrixBInv
    simp only [mul_assoc]
  · change (matrixA * matrixB) * matrixA * (matrixBInv * matrixA) =
      matrixA * (matrixB * matrixA * matrixBInv) * matrixA
    simp only [mul_assoc]
  · change (1 : Matrix (Fin 45) (Fin 45) (ZMod 7)) * matrixA * 1 = matrixA
    simp
  · rfl
end ONan.Simplicity.TwoCertificate.Fusion
