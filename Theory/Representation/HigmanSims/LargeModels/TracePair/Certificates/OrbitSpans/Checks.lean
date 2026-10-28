module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnData
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.RowData
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.PackedGenerators

/-!
# Numerical contracts for the published HS spanning orbits

The four outstanding equations are the two literal orbit recursions and the
left inverses of their row matrices. The bridges below accept checked packed
products and derive matrix equations over Four. The column recursion explicitly
uses `mulVec`, even though its vectors are stored as rows.

Source: `Certificates/source/README.md` and `witnesses.json.gz`.
The consumer is `Certificates/OrbitSpans.lean`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans

/-- The source letters 0 and 1 select the common packed generators A and B. -/
def packedLetter (letter : ℕ) : Packed.Mat :=
  if letter = 0 then generatorRowsA else generatorRowsB

theorem packedLetter_length (letter : ℕ) : (packedLetter letter).length = 896 := by
  unfold packedLetter
  split
  · exact generatorRowsA_length
  · exact generatorRowsB_length

/-- The precise outstanding column-action equations over the shared packed data. -/
def ColumnRecursion : Prop := ∀ i : Fin 895,
  columnMatrix i.succ =
    (Packed.eval 896 (packedLetter (columnLetters.getD i.val 0))).mulVec
      (columnMatrix (columnParent i))

/-- The precise outstanding row-action equations over the shared packed data. -/
def RowRecursion : Prop := ∀ i : Fin 895,
  rowMatrix i.succ = Matrix.vecMul (rowMatrix (rowParent i))
    (Packed.eval 896 (packedLetter (rowLetters.getD i.val 0)))

/-- Sound connection from packed row products to the literal left-inverse equation. -/
theorem column_inverse_of_products
    (h : ∀ i : Fin 896,
      Packed.rowProduct (columnInverseRows.getD i.val (0, 0)) columnRows = (2 ^ i.val, 0)) :
    columnInverse * columnMatrix = 1 :=
  Packed.eval_inverse 896 columnInverseRows columnRows columnRows_length h

theorem row_inverse_of_products
    (h : ∀ i : Fin 896,
      Packed.rowProduct (rowInverseRows.getD i.val (0, 0)) rowRows = (2 ^ i.val, 0)) :
    rowInverse * rowMatrix = 1 :=
  Packed.eval_inverse 896 rowInverseRows rowRows rowRows_length h

/-- The row recursion can use the existing whole-row packed product checker. -/
theorem row_recursion_of_products
    (h : ∀ i : Fin 895,
      Packed.rowProduct (rowRows.getD (rowParent i).val (0, 0))
        (packedLetter (rowLetters.getD i.val 0)) = rowRows.getD i.succ.val (0, 0)) :
    RowRecursion := by
  intro i
  funext j
  change Packed.decode (rowRows.getD i.succ.val (0, 0)) j.val =
    ∑ k : Fin 896, Packed.decode (rowRows.getD (rowParent i).val (0, 0)) k.val *
      Packed.decode ((packedLetter (rowLetters.getD i.val 0)).getD k.val (0, 0)) j.val
  rw [← Packed.decode_rowProduct _ _ 896 (packedLetter_length _), h i]

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans
