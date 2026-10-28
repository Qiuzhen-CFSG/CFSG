module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient.IntegralKernel.Data
/-!
# Sparse row formulas for the integral generators

These identities expand right multiplication by the literal ATLAS matrices
from `MatrixData`. They remove zero summands before the finite certificate
checks, while retaining the original row-action convention and scalar ring.
Numerical source: John Bray, `6L34G1-Ar6aB0.M`, as recorded in `MatrixData`.
-/

@[expose] public section
open Atlas.Algebra Matrix
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.IntegralKernel

def stepA (v : Row) : Row := ![-v 0, v 2, v 1, v 4, v 3, -v 5]
def stepB (v : Row) : Row :=
  let w := eisensteinOmega
  ![-v 4, v 0 - v 1 - v 4, -v 2 + v 3 * (-w-1),
    v 4 * (w+1) - v 5, v 1, v 1 * (w+1) + v 3]
def stepBInv (v : Row) : Row :=
  let w := eisensteinOmega
  ![-v 0 + v 1 + v 4, v 4, -v 2 + v 4 * w + v 5 * (-w-1),
    v 4 * (-w-1) + v 5, -v 0, v 0 * (-w-1) - v 3]

theorem stepA_eq (v : Row) : stepA v = v ᵥ* matrixA := by
  funext j
  fin_cases j <;> simp [stepA, matrixA, vecMul, dotProduct, Fin.sum_univ_succ]
theorem stepB_eq (v : Row) : stepB v = v ᵥ* matrixB := by
  funext j
  fin_cases j <;> simp [stepB, matrixB, vecMul, dotProduct, Fin.sum_univ_succ] <;> ring
theorem stepBInv_eq (v : Row) : stepBInv v = v ᵥ* matrixBInv := by
  funext j
  fin_cases j <;> simp [stepBInv, matrixBInv, vecMul, dotProduct, Fin.sum_univ_succ] <;> ring
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.IntegralKernel
