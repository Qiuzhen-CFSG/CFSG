module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Basic
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.TransposeData

/-!
# Connecting individual packed equations to the column certificate ranges

Each numerical proof retains the literal source lookup and product equation.
These bridges assemble the checked equations without evaluating them a second
time during conversion to the range predicates. The source is the unchanged
`Certificates/source/witnesses.json.gz`; see `ColumnChecks/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks

theorem inverseStep_of_packed (i : Nat)
    (h : Packed.rowProduct (columnInverseRows.getD i (0,0)) columnRows = (2^i,0)) :
    inverseStep i = true := by
  unfold inverseStep
  apply beq_iff_eq.mpr
  rw [fastProduct_eq]
  exact h

theorem recursionStep_of_packed (i : Nat)
    (h : Packed.rowProduct (columnRows.getD (columnParents.getD i 0) (0,0))
      (if columnLetters.getD i 0 = 0 then transposedRowsA else transposedRowsB) =
      columnRows.getD (i+1) (0,0)) :
    recursionStep transposedRowsA transposedRowsB i = true := by
  unfold recursionStep
  apply beq_iff_eq.mpr
  rw [fastProduct_eq]
  exact h

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks
