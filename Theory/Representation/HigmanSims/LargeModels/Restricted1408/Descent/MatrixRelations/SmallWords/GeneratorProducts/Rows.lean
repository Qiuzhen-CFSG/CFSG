module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch00
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch01
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch02
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch03
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch04
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch05
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch06
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch07
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch08
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch09
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch10
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch11
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch12
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch13
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch14
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch15
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch16
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch17
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch18
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch19
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch20
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Batch21

/-!
# Complete row certificates for the four generator products

The 22 batches partition all 1408 coordinates into intervals of length 64.
This assembly uses Euclidean division to select the batch and its local row;
there are no omitted coordinates. See `source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts.GeneratorCertificate
open PackedBinaryRows

/-- The exact packed-row equation at every one of the 1408 coordinates. -/
theorem a_a_rows (i : Fin 1408) :
    listProduct aRows[i.val]! 0 aRows.toList = 2 ^ i.val := by
  have h : ∀ j : Fin 22, ∀ k : Fin 64,
      listProduct aRows[64 * j.val + k.val]! 0 aRows.toList = 2 ^ (64 * j.val + k.val) :=
    Fin.cases Batch00.a_a (Fin.cases Batch01.a_a (Fin.cases Batch02.a_a (Fin.cases Batch03.a_a (Fin.cases Batch04.a_a (Fin.cases Batch05.a_a (Fin.cases Batch06.a_a (Fin.cases Batch07.a_a (Fin.cases Batch08.a_a (Fin.cases Batch09.a_a (Fin.cases Batch10.a_a (Fin.cases Batch11.a_a (Fin.cases Batch12.a_a (Fin.cases Batch13.a_a (Fin.cases Batch14.a_a (Fin.cases Batch15.a_a (Fin.cases Batch16.a_a (Fin.cases Batch17.a_a (Fin.cases Batch18.a_a (Fin.cases Batch19.a_a (Fin.cases Batch20.a_a (Fin.cases Batch21.a_a (fun i => Fin.elim0 i))))))))))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

/-- The exact packed-row equation at every one of the 1408 coordinates. -/
theorem b_b_rows (i : Fin 1408) :
    listProduct bRows[i.val]! 0 bRows.toList = b2Rows[i.val]! := by
  have h : ∀ j : Fin 22, ∀ k : Fin 64,
      listProduct bRows[64 * j.val + k.val]! 0 bRows.toList = b2Rows[64 * j.val + k.val]! :=
    Fin.cases Batch00.b_b (Fin.cases Batch01.b_b (Fin.cases Batch02.b_b (Fin.cases Batch03.b_b (Fin.cases Batch04.b_b (Fin.cases Batch05.b_b (Fin.cases Batch06.b_b (Fin.cases Batch07.b_b (Fin.cases Batch08.b_b (Fin.cases Batch09.b_b (Fin.cases Batch10.b_b (Fin.cases Batch11.b_b (Fin.cases Batch12.b_b (Fin.cases Batch13.b_b (Fin.cases Batch14.b_b (Fin.cases Batch15.b_b (Fin.cases Batch16.b_b (Fin.cases Batch17.b_b (Fin.cases Batch18.b_b (Fin.cases Batch19.b_b (Fin.cases Batch20.b_b (Fin.cases Batch21.b_b (fun i => Fin.elim0 i))))))))))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

/-- The exact packed-row equation at every one of the 1408 coordinates. -/
theorem b2_b2_rows (i : Fin 1408) :
    listProduct b2Rows[i.val]! 0 b2Rows.toList = inverseRows[i.val]! := by
  have h : ∀ j : Fin 22, ∀ k : Fin 64,
      listProduct b2Rows[64 * j.val + k.val]! 0 b2Rows.toList = inverseRows[64 * j.val + k.val]! :=
    Fin.cases Batch00.b2_b2 (Fin.cases Batch01.b2_b2 (Fin.cases Batch02.b2_b2 (Fin.cases Batch03.b2_b2 (Fin.cases Batch04.b2_b2 (Fin.cases Batch05.b2_b2 (Fin.cases Batch06.b2_b2 (Fin.cases Batch07.b2_b2 (Fin.cases Batch08.b2_b2 (Fin.cases Batch09.b2_b2 (Fin.cases Batch10.b2_b2 (Fin.cases Batch11.b2_b2 (Fin.cases Batch12.b2_b2 (Fin.cases Batch13.b2_b2 (Fin.cases Batch14.b2_b2 (Fin.cases Batch15.b2_b2 (Fin.cases Batch16.b2_b2 (Fin.cases Batch17.b2_b2 (Fin.cases Batch18.b2_b2 (Fin.cases Batch19.b2_b2 (Fin.cases Batch20.b2_b2 (Fin.cases Batch21.b2_b2 (fun i => Fin.elim0 i))))))))))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

/-- The exact packed-row equation at every one of the 1408 coordinates. -/
theorem inverse_b_rows (i : Fin 1408) :
    listProduct inverseRows[i.val]! 0 bRows.toList = 2 ^ i.val := by
  have h : ∀ j : Fin 22, ∀ k : Fin 64,
      listProduct inverseRows[64 * j.val + k.val]! 0 bRows.toList = 2 ^ (64 * j.val + k.val) :=
    Fin.cases Batch00.inverse_b (Fin.cases Batch01.inverse_b (Fin.cases Batch02.inverse_b (Fin.cases Batch03.inverse_b (Fin.cases Batch04.inverse_b (Fin.cases Batch05.inverse_b (Fin.cases Batch06.inverse_b (Fin.cases Batch07.inverse_b (Fin.cases Batch08.inverse_b (Fin.cases Batch09.inverse_b (Fin.cases Batch10.inverse_b (Fin.cases Batch11.inverse_b (Fin.cases Batch12.inverse_b (Fin.cases Batch13.inverse_b (Fin.cases Batch14.inverse_b (Fin.cases Batch15.inverse_b (Fin.cases Batch16.inverse_b (Fin.cases Batch17.inverse_b (Fin.cases Batch18.inverse_b (Fin.cases Batch19.inverse_b (Fin.cases Batch20.inverse_b (Fin.cases Batch21.inverse_b (fun i => Fin.elim0 i))))))))))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts.GeneratorCertificate
