module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch00
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch01
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch02
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch03
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch04
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch05
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch06
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch07
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch08
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch09
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch10
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch11
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch12
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Batch13

/-!
# Complete row equations for the three fixed products

The fourteen certified batches partition all 896 coordinates. Euclidean
division selects each batch and its local row, so no coordinate is omitted.
These equations concern the unchanged literal C, C2 and C4 tables; they do
not assume that C is the source word. See `source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.OrderRows
open Certificates OrderBatches

/-- The fixed product equation at every coordinate row. -/
theorem square_rows (i : Fin 896) :
    Streaming.product (commutatorRows.getD i.val (0, 0)) commutatorRows = commutatorTwoRows.getD i.val (0, 0) := by
  have h : ∀ j : Fin 14, ∀ k : Fin 64,
      Streaming.product (commutatorRows.getD (64 * j.val + k.val) (0, 0)) commutatorRows =
        commutatorTwoRows.getD (64 * j.val + k.val) (0, 0) :=
    Fin.cases Batch00.square (Fin.cases Batch01.square (Fin.cases Batch02.square (Fin.cases Batch03.square (Fin.cases Batch04.square (Fin.cases Batch05.square (Fin.cases Batch06.square (Fin.cases Batch07.square (Fin.cases Batch08.square (Fin.cases Batch09.square (Fin.cases Batch10.square (Fin.cases Batch11.square (Fin.cases Batch12.square (Fin.cases Batch13.square (fun i => Fin.elim0 i))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

/-- The fixed product equation at every coordinate row. -/
theorem square_two_rows (i : Fin 896) :
    Streaming.product (commutatorTwoRows.getD i.val (0, 0)) commutatorTwoRows = commutatorFourRows.getD i.val (0, 0) := by
  have h : ∀ j : Fin 14, ∀ k : Fin 64,
      Streaming.product (commutatorTwoRows.getD (64 * j.val + k.val) (0, 0)) commutatorTwoRows =
        commutatorFourRows.getD (64 * j.val + k.val) (0, 0) :=
    Fin.cases Batch00.square_two (Fin.cases Batch01.square_two (Fin.cases Batch02.square_two (Fin.cases Batch03.square_two (Fin.cases Batch04.square_two (Fin.cases Batch05.square_two (Fin.cases Batch06.square_two (Fin.cases Batch07.square_two (Fin.cases Batch08.square_two (Fin.cases Batch09.square_two (Fin.cases Batch10.square_two (Fin.cases Batch11.square_two (Fin.cases Batch12.square_two (Fin.cases Batch13.square_two (fun i => Fin.elim0 i))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

/-- The fixed product equation at every coordinate row. -/
theorem four_times_rows (i : Fin 896) :
    Streaming.product (commutatorFourRows.getD i.val (0, 0)) commutatorRows = (2 ^ i.val, 0) := by
  have h : ∀ j : Fin 14, ∀ k : Fin 64,
      Streaming.product (commutatorFourRows.getD (64 * j.val + k.val) (0, 0)) commutatorRows =
        (2 ^ (64 * j.val + k.val), 0) :=
    Fin.cases Batch00.four_times (Fin.cases Batch01.four_times (Fin.cases Batch02.four_times (Fin.cases Batch03.four_times (Fin.cases Batch04.four_times (Fin.cases Batch05.four_times (Fin.cases Batch06.four_times (Fin.cases Batch07.four_times (Fin.cases Batch08.four_times (Fin.cases Batch09.four_times (Fin.cases Batch10.four_times (Fin.cases Batch11.four_times (Fin.cases Batch12.four_times (Fin.cases Batch13.four_times (fun i => Fin.elim0 i))))))))))))))
  have hrow := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩
  have he : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [he] using hrow

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.OrderRows
