module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.LinearAlgebra

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

theorem entry_map_of_lt (xs : List ℕ) (f : ℕ → ℕ) (i : ℕ) (hi : i < xs.length) :
    entry (xs.map f) i = f (entry xs i) := by
  simp only [entry, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

set_option maxRecDepth 8192 in
 theorem packed_of_traversals
    (h0 : forwardRows0.map (fun i => combineList (rows252 0)
      (entry covectorRows (i % 1771))) = covectorRows)
    (h1 : forwardRows1.map (fun i => combineList (rows252 1)
      (entry covectorRows (i % 1771))) = covectorRows) :
    ∀ j i, combineList (rows252 j) (entry covectorRows (forward j i).val) =
      entry covectorRows i.val := by
  intro j i
  fin_cases j
  · have hl : forwardRows0.length = 1771 := by decide +kernel
    have ht := congrArg (fun xs => entry xs i.val) h0
    rw [entry_map_of_lt _ _ _ (by simpa only [hl] using i.isLt)] at ht
    exact ht
  · have hl : forwardRows1.length = 1771 := by decide +kernel
    have ht := congrArg (fun xs => entry xs i.val) h1
    rw [entry_map_of_lt _ _ _ (by simpa only [hl] using i.isLt)] at ht
    exact ht

set_option maxRecDepth 8192 in
 theorem inverse_of_rows
    (h : inverseRows.map (combineList selectedRows) =
      (List.range 252).map (fun i => 2 ^ i)) : Native252.inverseMatrix * selectedMatrix = 1 := by
  have hi : inverseRows.length = 252 := by decide +kernel
  have hs : selectedRows.length = 252 := by decide +kernel
  have ht := matrix_product inverseRows selectedRows
    ((List.range 252).map (fun i => 2 ^ i)) hs
    (product_rows _ _ _ hi h)
  change matrix inverseRows * matrix selectedRows = 1
  rw [ht]
  ext i k
  simp only [matrix, vector, entry, List.getElem?_map, List.getElem?_range i.isLt,
    Option.map_some, Option.getD_some, bit_power, Matrix.one_apply, Fin.val_inj]


set_option maxRecDepth 8192 in
theorem rows252_length : ∀ j, (rows252 j).length = 252 := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.MatrixCertificates
