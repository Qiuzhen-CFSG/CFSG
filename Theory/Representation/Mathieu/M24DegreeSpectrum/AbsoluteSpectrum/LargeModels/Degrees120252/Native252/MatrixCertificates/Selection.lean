module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates.Support

/-!
# Kernel checks for the native sextet embedding

The data describe the 1771-by-252 embedding in the native sextet permutation
space. The checks retain the literal ordering and the forward-index convention.
All numerical equalities are reduced by the Lean kernel. Sources: James,
J. Algebra 27 (1973), 57–111; GM02, Proposition 5.1; the saved ATLAS candidates
and sextet construction documented in `../../source/README.md`.
-/

set_option Elab.async false
public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks

set_option maxRecDepth 8192 in
private theorem selected_rows_check :
    selectedIndices.map (fun i => entry covectorRows (i % 1771)) = selectedRows := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- The saved square matrix consists of exactly the selected embedding rows. -/
theorem selected_rows (i : Fin 252) (k : Fin 252) :
    embeddingMatrix (selectedIndex i) k = selectedMatrix i k := by
  have hl : selectedIndices.length = 252 := by decide +kernel
  have ht := congrArg (fun xs => entry xs i.val) selected_rows_check
  rw [entry_map_of_lt _ _ _ (by simpa only [hl] using i.isLt)] at ht
  exact congrArg (fun x => bit x k.val) ht

set_option maxRecDepth 8192 in
private theorem inverse_chunk0 :
    inverseRowsChunk0.map (combineList selectedRows) =
      (List.range' 0 64).map (fun i => 2 ^ i) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem inverse_chunk1 :
    inverseRowsChunk1.map (combineList selectedRows) =
      (List.range' 64 64).map (fun i => 2 ^ i) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem inverse_chunk2 :
    inverseRowsChunk2.map (combineList selectedRows) =
      (List.range' 128 64).map (fun i => 2 ^ i) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem inverse_chunk3 :
    inverseRowsChunk3.map (combineList selectedRows) =
      (List.range' 192 60).map (fun i => 2 ^ i) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem inverse_traversal :
    inverseRows.map (combineList selectedRows) = (List.range 252).map (fun i => 2 ^ i) := by
  simp only [inverseRows, List.map_flatten, List.map_cons, List.map_nil,
    inverse_chunk0, inverse_chunk1, inverse_chunk2, inverse_chunk3]
  decide +kernel

/-- The inverse is on the left, as required for injection of column vectors. -/
theorem inverse_mul_selected : inverseMatrix * selectedMatrix = 1 :=
  inverse_of_rows inverse_traversal

/-- The full rectangular matrix embeds the 252-dimensional space. -/
theorem embedding_injective : Function.Injective embedding :=
  embedding_injective_of_inverse selected_rows inverse_mul_selected

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates
