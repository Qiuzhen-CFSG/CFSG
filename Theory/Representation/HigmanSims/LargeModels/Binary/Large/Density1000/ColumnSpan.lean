module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Trees
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.PackedSpan

/-!
# The literal degree-1000 column orbit spans

The checked left inverse proves that the packed candidate columns span. The
checked generator transposes and prepended-word transitions identify those
columns with the literal source-word images. Combining these two certificates
proves `columnOrbit_span` without additional hypotheses. The conditional
arithmetic and word-induction interfaces remain available below.

Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0 and
`Binary/source/density1000.json`; see `ColumnSpan/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000
open Thompson.BinaryMatrix RowArithmetic

/-- Final assembly retains both independent numerical obligations. -/
theorem columnOrbit_span_of_realizations
    (hwords : ∀ i : Fin 1000, columnOrbit i = vector 1000 Data.columnRows[i.val]!)
    (hspan : Submodule.span (ZMod 2)
      (Set.range (fun i : Fin 1000 => vector 1000 Data.columnRows[i.val]!)) = ⊤) :
    Submodule.span (ZMod 2) (Set.range columnOrbit) = ⊤ := by
  rw [show columnOrbit = (fun i : Fin 1000 => vector 1000 Data.columnRows[i.val]!)
    from funext hwords]
  exact hspan

/-- The literal published word images of the source image vector span all coordinates. -/
theorem columnOrbit_span :
    Submodule.span (ZMod 2) (Set.range columnOrbit) = ⊤ :=
  columnOrbit_span_of_realizations columnOrbit_eq ColumnSpan.packedColumns_span

namespace ColumnSpan

/-- The inverse checker feeds the exact shared packed-column spanning statement. -/
theorem packedColumns_span_of_checks
    (h : On (fun i => decide (columnTree.product (inverseTree.get i) = 2 ^ i) = true) 0 1000) :
    Submodule.span (ZMod 2)
      (Set.range (fun i : Fin 1000 => vector 1000 Data.columnRows[i.val]!)) = ⊤ := by
  have hinv := inverse_of_checks columnTree inverseTree Data.columnRows Data.columnInverseRows 1000
    columnTree_valid inverseTree_valid columnTree_rows inverseTree_rows (by decide +kernel) h
  exact Small.Packed.span_rows_of_inverse Data.columnRows Data.columnInverseRows hinv

/-- Checked transposes and prepended-word steps yield literal orbit identifications. -/
theorem columnOrbit_eq_of_checks
    (ha : On (fun i => aTransposeTree.columnMatch (2 ^ i) (aTree.get i) = true) 0 1000)
    (hb : On (fun i => bTransposeTree.columnMatch (2 ^ i) (bTree.get i) = true) 0 1000)
    (hs : On (OrbitStep aTransposeTree bTransposeTree columnTree wordTree) 1 1000) :
    ∀ i : Fin 1000, columnOrbit i = vector 1000 Data.columnRows[i.val]! := by
  have hat := transpose_of_checks aTransposeTree aTree D1000.aRows 1000
    aTransposeTree_valid aTree_valid aTree_rows aTransposeTree_length ha
  have hbt := transpose_of_checks bTransposeTree bTree D1000.bRows 1000
    bTransposeTree_valid bTree_valid bTree_rows bTransposeTree_length hb
  exact orbits_of_steps aTransposeTree bTransposeTree columnTree wordTree
    aTransposeTree_valid bTransposeTree_valid columnTree_valid wordTree_valid
    columnTree_rows wordTree_rows aTransposeTree_length bTransposeTree_length hat hbt hs

end ColumnSpan
open ColumnSpan

/-- Alternative assembly from the four explicit finite-check families. -/
theorem columnOrbit_span_of_checked_tables
    (hi : On (fun i => decide (columnTree.product (inverseTree.get i) = 2 ^ i) = true) 0 1000)
    (ha : On (fun i => aTransposeTree.columnMatch (2 ^ i) (aTree.get i) = true) 0 1000)
    (hb : On (fun i => bTransposeTree.columnMatch (2 ^ i) (bTree.get i) = true) 0 1000)
    (hs : On (OrbitStep aTransposeTree bTransposeTree columnTree wordTree) 1 1000) :
    Submodule.span (ZMod 2) (Set.range columnOrbit) = ⊤ :=
  columnOrbit_span_of_realizations (columnOrbit_eq_of_checks ha hb hs) (packedColumns_span_of_checks hi)

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000
