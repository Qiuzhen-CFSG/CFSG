module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Blocks
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Tables.A
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Tables.B
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Tables.D
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Tables.ONE

/-!
# Aligning the bounded certificate rows with the original ATLAS arrays

These checks connect the computational tables to the original generators,
the shared D tree, and the identity matrix. They assert no generator product.
Attribution and source conventions: `Binary/source/README.md`.
-/

public section
open Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra
open Tables RowArithmetic

theorem a_aligned : aRows = D1000.aRows.toList := by decide +kernel

theorem b_aligned : bRows = D1000.bRows.toList := by decide +kernel

theorem d_aligned : dRows = dTree.rows := by decide +kernel

theorem one_aligned : oneRows = List.ofFn (fun i : Fin 1000 => 2^i.val) := by
  decide +kernel

theorem a_matrix : matrix 1000 1000 aRows = decode 1000 D1000.aRows := by
  rw [a_aligned, matrix_toList]

theorem b_matrix : matrix 1000 1000 bRows = decode 1000 D1000.bRows := by
  rw [b_aligned, matrix_toList]

theorem d_matrix : matrix 1000 1000 dRows = decode 1000 Data.dRows := by
  rw [d_aligned, dTree_aligned, matrix_toList]

theorem one_matrix : matrix 1000 1000 oneRows = 1 := by
  rw [one_aligned, matrix_identity_rows]

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra
