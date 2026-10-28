module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.Closure
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.Checks
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.RowChecks
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.DensityCriterion

/-!
# Applying the published HS orbit certificates to matrix-algebra density

The saved column vectors are stored as rows, but their recursion uses `mulVec`.
The saved row vectors use `vecMul`. Parent-index induction places every vector
in the actual algebra orbit of the normalized null vector. A checked left
inverse then proves the corresponding orbit span is the whole vector space.

The two numerical recursions and left inverses are checked in `ColumnChecks`
and `RowChecks`. The final span theorems retain only the two shared generator
re-encoding equations. The density consumer additionally takes membership of
the null projector in the generated algebra, supplied independently.

Source: `Certificates/source/README.md` and `witnesses.json.gz`. The exact data
and checked numerical contracts are documented in `OrbitSpans/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates
namespace OrbitSpans

theorem packedLetter_mem
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB) (letter : ℕ) :
    Packed.eval 896 (packedLetter letter) ∈ generated := by
  unfold packedLetter
  split
  · rw [hA]; exact matrixA_mem
  · rw [hB]; exact matrixB_mem

end OrbitSpans
open OrbitSpans

/-- Actual generated-algebra column orbit, conditional only on the displayed
finite certificates and the common generator interpretations. -/
theorem columnOrbitSpan_eq_top_of_checks
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB)
    (hstep : ColumnRecursion) (hinverse : columnInverse * columnMatrix = 1) :
    columnOrbitSpan = ⊤ := by
  apply eq_top_of_left_inverse columnOrbitSpan columnMatrix columnInverse hinverse
  intro i
  obtain ⟨M, hM, he⟩ := column_translates generated
    (fun k => Packed.eval 896 (packedLetter (columnLetters.getD k.val 0)))
    (fun k => packedLetter_mem hA hB _) nullColumn columnMatrix columnParent
    columnParent_le column_root hstep i
  exact Submodule.subset_span ⟨⟨M, hM⟩, he⟩

/-- Actual generated-algebra row orbit, with the source's right action. -/
theorem rowOrbitSpan_eq_top_of_checks
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB)
    (hstep : RowRecursion) (hinverse : rowInverse * rowMatrix = 1) :
    rowOrbitSpan = ⊤ := by
  apply eq_top_of_left_inverse rowOrbitSpan rowMatrix rowInverse hinverse
  intro i
  obtain ⟨M, hM, he⟩ := row_translates generated
    (fun k => Packed.eval 896 (packedLetter (rowLetters.getD k.val 0)))
    (fun k => packedLetter_mem hA hB _) nullRow rowMatrix rowParent
    rowParent_le row_root hstep i
  exact Submodule.subset_span ⟨⟨M, hM⟩, he⟩

/-- The published column orbit spans, using the checked recursion and left
inverse. Only interpretation of the common packed generators remains explicit. -/
theorem columnOrbitSpan_eq_top_of_reencoding
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB) : columnOrbitSpan = ⊤ :=
  columnOrbitSpan_eq_top_of_checks hA hB column_recursion_checked column_inverse_checked

/-- The published row orbit spans under the source's right action, conditional
only on interpretation of the common packed generators. -/
theorem rowOrbitSpan_eq_top_of_reencoding
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB) : rowOrbitSpan = ⊤ :=
  rowOrbitSpan_eq_top_of_checks hA hB row_recursion_checked row_inverse_checked

/-- Literal application to the existing density criterion. Projector membership
is supplied by the independent null-projector certificate owner. -/
theorem full_of_orbit_checks
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB)
    (hP : Matrix.vecMulVec nullColumn nullRow ∈ generated)
    (hc : ColumnRecursion) (hci : columnInverse * columnMatrix = 1)
    (hr : RowRecursion) (hri : rowInverse * rowMatrix = 1) : MatrixAlgebraFull :=
  full_of_nullProjector hP (columnOrbitSpan_eq_top_of_checks hA hB hc hci)
    (rowOrbitSpan_eq_top_of_checks hA hB hr hri)

/-- The checked orbits discharge both spanning premises of the literal density
criterion. Null-projector membership and generator interpretation remain explicit. -/
theorem full_of_nullProjector_of_reencoding
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB)
    (hP : Matrix.vecMulVec nullColumn nullRow ∈ generated) : MatrixAlgebraFull :=
  full_of_nullProjector hP (columnOrbitSpan_eq_top_of_reencoding hA hB)
    (rowOrbitSpan_eq_top_of_reencoding hA hB)

end Representation.HigmanSims.LargeModels.TracePair.Certificates
