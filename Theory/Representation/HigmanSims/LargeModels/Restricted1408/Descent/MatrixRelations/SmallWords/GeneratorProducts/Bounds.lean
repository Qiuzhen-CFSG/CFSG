module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.RowsA
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.RowsB
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.InverseRows
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.B2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Arithmetic

/-! Width and length certificates for the unchanged right-hand row tables.
They justify carry-free simultaneous row multiplication; see `source/README.md`. -/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts.GeneratorCertificate

theorem aRows_length : aRows.toList.length ≤ 1408 := by decide +kernel

theorem aRows_bounded : ∀ r ∈ aRows.toList, r < 2 ^ 1408 := by
  have h : aRows.toList.all (fun r => decide (r < 2 ^ 1408)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem bRows_length : bRows.toList.length ≤ 1408 := by decide +kernel

theorem bRows_bounded : ∀ r ∈ bRows.toList, r < 2 ^ 1408 := by
  have h : bRows.toList.all (fun r => decide (r < 2 ^ 1408)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem b2Rows_length : b2Rows.toList.length ≤ 1408 := by decide +kernel

theorem b2Rows_bounded : ∀ r ∈ b2Rows.toList, r < 2 ^ 1408 := by
  have h : b2Rows.toList.all (fun r => decide (r < 2 ^ 1408)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts.GeneratorCertificate
