module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Numbers

/-!
# Assembling exact column-recursion equations

The checked products use the literal parent and letter arrays. This generic
bridge converts equality to the range predicate without another numerical
conversion. See `ColumnChecks/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks

theorem recursionStep_of_fast (i : Nat)
    (h : fastProduct (columnRows.getD (columnParents.getD i 0) (0,0))
      (if columnLetters.getD i 0 = 0 then transposedRowsA else transposedRowsB) =
      columnRows.getD (i+1) (0,0)) :
    recursionStep transposedRowsA transposedRowsB i = true := by
  exact beq_iff_eq.mpr h

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks
