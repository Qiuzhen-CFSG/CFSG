module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates.Rows.Checks

/-!
# Assembly of all native generator equations

Mapping over the flattened blocks combines all 1771 checked rows. The covector
table remains folded until the individual block equalities are applied.

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

theorem generator0_traversal :
    forwardRows0.map (fun i => combineList (rows252 0)
      (entry covectorRows (i % 1771))) = covectorRows := by
  rw [forwardRows0, List.map_flatten]
  simp only [List.map_cons, List.map_nil,
    chunk0_00, chunk0_01, chunk0_02, chunk0_03, chunk0_04, chunk0_05, chunk0_06, chunk0_07, chunk0_08, chunk0_09, chunk0_10, chunk0_11, chunk0_12, chunk0_13, chunk0_14, chunk0_15, chunk0_16, chunk0_17, chunk0_18, chunk0_19, chunk0_20, chunk0_21, chunk0_22, chunk0_23, chunk0_24, chunk0_25, chunk0_26, chunk0_27]
  rfl

theorem generator1_traversal :
    forwardRows1.map (fun i => combineList (rows252 1)
      (entry covectorRows (i % 1771))) = covectorRows := by
  rw [forwardRows1, List.map_flatten]
  simp only [List.map_cons, List.map_nil,
    chunk1_00, chunk1_01, chunk1_02, chunk1_03, chunk1_04, chunk1_05, chunk1_06, chunk1_07, chunk1_08, chunk1_09, chunk1_10, chunk1_11, chunk1_12, chunk1_13, chunk1_14, chunk1_15, chunk1_16, chunk1_17, chunk1_18, chunk1_19, chunk1_20, chunk1_21, chunk1_22, chunk1_23, chunk1_24, chunk1_25, chunk1_26, chunk1_27]
  rfl

/-- Every covector row, for both literal generators. -/
theorem packed_rows : ∀ j i,
    combineList (rows252 j) (entry covectorRows (forward j i).val) =
      entry covectorRows i.val :=
  packed_of_traversals generator0_traversal generator1_traversal

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates
