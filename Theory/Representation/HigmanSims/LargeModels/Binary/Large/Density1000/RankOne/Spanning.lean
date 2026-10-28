module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Inverse
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Packed

/-!
# Spanning of the degree-1000 Krylov rows

The eight bounded inverse certificates prove that the candidate inverse matrix
is a left inverse of the literal matrix whose rows are `krylovRows`.  The
standard packed-row range argument then identifies the span of the decoded
chain with the full coordinate space.  This is independent of the generator
identification and of the cyclic transition certificates.

The numerical rows are the candidate generated from the ATLAS HSG1-f2r1000B0
tables; attribution and rights are retained in `Binary/source/README.md`.
-/

@[expose] public section
open Matrix Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
open RowArithmetic

/-- The checked candidate inverse is a left inverse of the Krylov row matrix. -/
theorem krylov_inverse :
    decode 1000 krylovInverseRows * decode 1000 krylovRows = 1 := by
  funext i
  apply RowArithmetic.decode_product_one_row 1000 krylovInverseRows krylovRows i
    krylovRows_size
  rw [← krylovTree_aligned, ← krylovTree.product_eq krylovTree_valid]
  exact all_inverse i.val (Nat.zero_le _) i.isLt

/-- The decoded Krylov chain spans all 1000 coordinates over `ZMod 2`. -/
theorem chain_span :
    Submodule.span (ZMod 2) (Set.range chain) = ⊤ := by
  change Submodule.span (ZMod 2)
    (Set.range (fun i : Fin 1000 => vector 1000 krylovRows[i.val]!)) = ⊤
  exact Small.Packed.span_rows_of_inverse krylovRows krylovInverseRows krylov_inverse

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
