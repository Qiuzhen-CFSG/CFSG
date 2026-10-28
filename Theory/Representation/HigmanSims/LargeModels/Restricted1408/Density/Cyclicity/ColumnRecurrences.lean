module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.CertificateInput
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.DataFacts
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.ProductCertificates
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.TransposeCertificates
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RecurrenceInput

/-!
# From packed certificates to the literal column-orbit recurrences

Every proposed step has its input, output and generator choice checked against
the unchanged published orbit. The transpose certificate compares each bit
against the literal aRows/bRows. Packed row multiplication then becomes ordinary
left multiplication by matrixA/matrixB through `Matrix.vecMul_transpose`.

The complete product and transpose certificates discharge both arithmetic
contracts, giving the unconditional `columnOrbitRecurrences` theorem.
No spanning, kernel-rank, irreducibility, density or carrier premise is used.
Source and certificate boundaries: `ColumnRecurrences/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
namespace ColumnRecurrences

/-- The column checker certifies the transpose of the ordinary binary decoder. -/
theorem decode_transpose_of_columnsCheck (n : Nat) (a t : Array Nat) (ht : t.size = n)
    (h : columnsCheck a.toList 0 t.toList = true) :
    Thompson.BinaryMatrix.decode n t = (Thompson.BinaryMatrix.decode n a).transpose := by
  ext i j
  have hi : i.val < t.toList.length := by simpa only [Array.length_toList, ht] using i.isLt
  have hc := columnsCheck_sound a.toList t.toList 0 h i.val hi
  simp only [Nat.zero_add, Array.getElem!_toList] at hc
  change Thompson.BinaryMatrix.bit t[i.val]! j.val = Thompson.BinaryMatrix.bit a[j.val]! i.val
  simp only [Thompson.BinaryMatrix.bit, ← hc, column_bit, Array.getElem!_toList]

theorem transposeA_decode (h : TransposeChecks) :
    Thompson.BinaryMatrix.decode 1408 transposeARows = matrixA.transpose :=
  decode_transpose_of_columnsCheck 1408 aRows transposeARows transposeARows_size h.1

theorem transposeB_decode (h : TransposeChecks) :
    Thompson.BinaryMatrix.decode 1408 transposeBRows = matrixB.transpose :=
  decode_transpose_of_columnsCheck 1408 bRows transposeBRows transposeBRows_size h.2

/-- Each checked packed step is the designated literal ordinary column action. -/
theorem step_mulVec (ht : TransposeChecks) (hp : ProductChecks) (s : Step) (hs : s ∈ steps) :
    vectorOfBits s.output =
      if s.choice then matrixB.mulVec (vectorOfBits s.input)
      else matrixA.mulVec (vectorOfBits s.input) := by
  have h := productsCheck_sound _ _ _ hp s hs
  cases hc : s.choice with
  | false =>
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    have ha := PackedBinaryRows.vecMul_decode_of_listProduct 1408 transposeARows
      s.input s.output transposeARows_size h
    rw [transposeA_decode ht, Matrix.vecMul_transpose] at ha
    exact ha.symm
  | true =>
    simp only [hc, ↓reduceIte] at h ⊢
    have hb := PackedBinaryRows.vecMul_decode_of_listProduct 1408 transposeBRows
      s.input s.output transposeBRows_size h
    rw [transposeB_decode ht, Matrix.vecMul_transpose] at hb
    exact hb.symm

end ColumnRecurrences
open ColumnRecurrences

/-- Exact recurrence assembly; both independent finite arithmetic contracts must be discharged. -/
theorem columnOrbitRecurrences_of_checks (ht : TransposeChecks) (hp : ProductChecks) :
    ColumnOrbitRecurrences := by
  intro i hi
  obtain ⟨s, hs, _, hin, hc, hout⟩ := steps_spec i hi
  simpa only [hin, hc, hout] using step_mulVec ht hp s hs

/-- Every positive-index column-orbit entry is the designated literal generator
acting on its published parent. -/
theorem columnOrbitRecurrences : ColumnOrbitRecurrences :=
  columnOrbitRecurrences_of_checks transposeChecks productChecks

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
