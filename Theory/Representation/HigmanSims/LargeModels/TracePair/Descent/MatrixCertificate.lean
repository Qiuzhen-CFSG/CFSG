module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.Words
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Data
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Finite matrix obligations for the degree-896 descent

The certificate contains invertible matrices with the literal ATLAS entries
and the thirteen explicit word equalities from `HSG1-P1.M`. These finite
equalities make no assertion about the permutation carrier. The independent
carrier-kernel theorem is also required by `Descent.lean`.

Source: ATLAS HSG1-f4r896aB0 and HSG1-P1.M; retained sources are in
`TracePair/source/` and `Descent/source/`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent

/-- Finite invertibility and relator checks on the exact published matrices.
This is a certificate interface, not an assertion that the checks hold. -/
structure MatrixRelatorCertificate where
  a : Matrix.GeneralLinearGroup (Fin 896) Four
  b : Matrix.GeneralLinearGroup (Fin 896) Four
  matrix_a : (a : Matrix (Fin 896) (Fin 896) Four) = matrixA
  matrix_b : (b : Matrix (Fin 896) (Fin 896) Four) = matrixB
  relations : ∀ i : Fin 13, relation a b i = 1

end Representation.HigmanSims.LargeModels.TracePair.Descent
