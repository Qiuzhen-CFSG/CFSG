module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.Data

/-!
# Transport of the native adjoint to the degree-120 matrix pair

An invertible linear comparison with both literal generator matrices transports
a lawful native action. Density is a separate premise in the application to
`BinaryModel`; this file makes no irreducibility inference from a dimension.

Source context: James, J. Algebra 27 (1973), 57–111; GM02, Proposition 5.1.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120

/-- The direction is native adjoint coordinates to the ATLAS column coordinates. -/
def comparisonEquiv
    (hCI : comparisonMatrix * inverseMatrix = 1)
    (hIC : inverseMatrix * comparisonMatrix = 1) :
    (Fin 120 → ZMod 2) ≃ₗ[ZMod 2] (Fin 120 → ZMod 2) :=
  Matrix.toLin'OfInv hIC hCI

/-- The exact algebraic assembly, with its native action and finite identities explicit. -/
def transportRealization (r : NativeRealization 120 adjointMatrix)
    (hCI : comparisonMatrix * inverseMatrix = 1)
    (hIC : inverseMatrix * comparisonMatrix = 1)
    (hC : ∀ j, comparisonMatrix * adjointMatrix j = matrix120 j * comparisonMatrix) :
    NativeRealization 120 matrix120 where
  representation := (comparisonEquiv hCI hIC).conjRingEquiv.toMonoidHom.comp r.representation
  matrix_actor j := by
    change LinearMap.toMatrix'
      (((Matrix.toLin' comparisonMatrix).comp (r.representation (actor j))).comp
        (Matrix.toLin' inverseMatrix)) = matrix120 j
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', r.matrix_actor]
    rw [hC, Matrix.mul_assoc, hCI, Matrix.mul_one]

/-- This consumes matrix density exactly as required by the parent assembly. -/
def binaryModelOfAdjoint (r : NativeRealization 120 adjointMatrix)
    (hCI : comparisonMatrix * inverseMatrix = 1)
    (hIC : inverseMatrix * comparisonMatrix = 1)
    (hC : ∀ j, comparisonMatrix * adjointMatrix j = matrix120 j * comparisonMatrix)
    (hA : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)),
      (∀ j, matrix120 j ∈ Q) → Q = ⊤) : BinaryModel 120 :=
  (transportRealization r hCI hIC hC).binaryModel hA

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
