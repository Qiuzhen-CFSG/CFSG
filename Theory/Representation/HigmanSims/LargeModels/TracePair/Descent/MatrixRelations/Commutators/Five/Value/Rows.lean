module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch00
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch01
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch02
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch03
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch04
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch05
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch06
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch07
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch08
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch09
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch10
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch11
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch12
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Batch13

/-!
# Complete row equations for the four remaining value products

The fourteen certified batches cover all 896 rows. Division by 64 selects
one batch and its local coordinate, so every original row is included.
These are fixed matrix products, with no candidate-to-word assumptions.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.ValueRows
open Certificates ValueBatches

/-- The fixed product equation at every original row. -/
theorem square_rows (i : Fin 896) :
    Streaming.product (bTwoRows.getD i.val (0, 0)) bTwoRows =
      bFourRows.getD i.val (0, 0) := by
  have h : ∀ j : Fin 14, ∀ k : Fin 64,
      Streaming.product (bTwoRows.getD (64 * j.val + k.val) (0, 0)) bTwoRows =
        bFourRows.getD (64 * j.val + k.val) (0, 0) :=
    Fin.cases Batch00.square ( Fin.cases Batch01.square ( Fin.cases Batch02.square ( Fin.cases Batch03.square ( Fin.cases Batch04.square ( Fin.cases Batch05.square ( Fin.cases Batch06.square ( Fin.cases Batch07.square ( Fin.cases Batch08.square ( Fin.cases Batch09.square ( Fin.cases Batch10.square ( Fin.cases Batch11.square ( Fin.cases Batch12.square ( Fin.cases Batch13.square (fun i => Fin.elim0 i))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

/-- The fixed product equation at every original row. -/
theorem left_a_rows (i : Fin 896) :
    Streaming.product (generatorRowsA.getD i.val (0, 0)) bFourRows =
      abFourRows.getD i.val (0, 0) := by
  have h : ∀ j : Fin 14, ∀ k : Fin 64,
      Streaming.product (generatorRowsA.getD (64 * j.val + k.val) (0, 0)) bFourRows =
        abFourRows.getD (64 * j.val + k.val) (0, 0) :=
    Fin.cases Batch00.left_a ( Fin.cases Batch01.left_a ( Fin.cases Batch02.left_a ( Fin.cases Batch03.left_a ( Fin.cases Batch04.left_a ( Fin.cases Batch05.left_a ( Fin.cases Batch06.left_a ( Fin.cases Batch07.left_a ( Fin.cases Batch08.left_a ( Fin.cases Batch09.left_a ( Fin.cases Batch10.left_a ( Fin.cases Batch11.left_a ( Fin.cases Batch12.left_a ( Fin.cases Batch13.left_a (fun i => Fin.elim0 i))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

/-- The fixed product equation at every original row. -/
theorem right_a_rows (i : Fin 896) :
    Streaming.product (abFourRows.getD i.val (0, 0)) generatorRowsA =
      abFourARows.getD i.val (0, 0) := by
  have h : ∀ j : Fin 14, ∀ k : Fin 64,
      Streaming.product (abFourRows.getD (64 * j.val + k.val) (0, 0)) generatorRowsA =
        abFourARows.getD (64 * j.val + k.val) (0, 0) :=
    Fin.cases Batch00.right_a ( Fin.cases Batch01.right_a ( Fin.cases Batch02.right_a ( Fin.cases Batch03.right_a ( Fin.cases Batch04.right_a ( Fin.cases Batch05.right_a ( Fin.cases Batch06.right_a ( Fin.cases Batch07.right_a ( Fin.cases Batch08.right_a ( Fin.cases Batch09.right_a ( Fin.cases Batch10.right_a ( Fin.cases Batch11.right_a ( Fin.cases Batch12.right_a ( Fin.cases Batch13.right_a (fun i => Fin.elim0 i))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

/-- The fixed product equation at every original row. -/
theorem right_b_rows (i : Fin 896) :
    Streaming.product (abFourARows.getD i.val (0, 0)) generatorRowsB =
      commutatorRows.getD i.val (0, 0) := by
  have h : ∀ j : Fin 14, ∀ k : Fin 64,
      Streaming.product (abFourARows.getD (64 * j.val + k.val) (0, 0)) generatorRowsB =
        commutatorRows.getD (64 * j.val + k.val) (0, 0) :=
    Fin.cases Batch00.right_b ( Fin.cases Batch01.right_b ( Fin.cases Batch02.right_b ( Fin.cases Batch03.right_b ( Fin.cases Batch04.right_b ( Fin.cases Batch05.right_b ( Fin.cases Batch06.right_b ( Fin.cases Batch07.right_b ( Fin.cases Batch08.right_b ( Fin.cases Batch09.right_b ( Fin.cases Batch10.right_b ( Fin.cases Batch11.right_b ( Fin.cases Batch12.right_b ( Fin.cases Batch13.right_b (fun i => Fin.elim0 i))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.ValueRows
