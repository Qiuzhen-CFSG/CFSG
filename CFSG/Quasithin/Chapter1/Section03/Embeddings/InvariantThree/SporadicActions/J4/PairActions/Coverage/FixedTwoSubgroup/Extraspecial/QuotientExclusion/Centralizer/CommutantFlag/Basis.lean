module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Centralizer.CommutantFlag.Data

/-!
# An invertible binary basis for the J₄ third-commutator certificate

Both products of the proposed basis and its inverse are checked using the
proved packed matrix multiplication interface. The resulting unit acts on
all binary matrices by conjugation, including singular matrices.
See `Data.lean` for the source and row convention.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ThirdFlag
open Janko4 Janko4.GeneratorCertificates

set_option maxRecDepth 10000

/-- The candidate inverse is a right inverse, checked row by row in the kernel. -/
theorem basis_mul_inverse : decodeRows basisRows * decodeRows inverseRows = 1 := by
  rw [← decode_packedMul, ← decode_packedOne]
  congr 1
  apply packedMul_eq_of_rows
  simp only [packedOne, get_ofFn]
  decide +kernel

/-- The candidate inverse is also a left inverse. -/
theorem inverse_mul_basis : decodeRows inverseRows * decodeRows basisRows = 1 := by
  rw [← decode_packedMul, ← decode_packedOne]
  congr 1
  apply packedMul_eq_of_rows
  simp only [packedOne, get_ofFn]
  decide +kernel

/-- The actual change of row basis, with both inverse identities proved. -/
def basisUnit : Janko4.BinaryMatrixˣ where
  val := decodeRows basisRows
  inv := decodeRows inverseRows
  val_inv := basis_mul_inverse
  inv_val := inverse_mul_basis

@[simp] theorem basisUnit_val : (basisUnit : Janko4.BinaryMatrix) =
    decodeRows basisRows := rfl

@[simp] theorem basisUnit_inv_val : (↑basisUnit⁻¹ : Janko4.BinaryMatrix) =
    decodeRows inverseRows := rfl

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ThirdFlag
