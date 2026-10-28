/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/GolayCoordinateSeparation.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSextetSigns
/-!
Golay coordinate restrictions and signed-support transport in the Leech lattice.
The proofs retain the explicit code maps and coordinate identities used by the stabilizer geometry.

Source: Gerald Höhn, `Atlas/Conway/GolayCoordinateSeparation.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem golay_coordinate_separates (i j : Omega) (hij : i ≠ j) :
    ∃ c : golay, c.val i ≠ c.val j := by
  classical
  by_contra h
  push Not at h
  let w := supportWord {i,j}
  have hw : w ∈ golay := by
    rw [golay_selfDual]
    intro c hc
    have he := h (⟨c,hc⟩ : golay)
    change binaryDot c (supportWord {i,j}) = 0
    rw [tetradSignParity_dot]
    change (∑ k : ({i,j} : Finset Omega), c k) = 0
    rw [Finset.sum_coe_sort]
    rw [Finset.sum_pair hij]
    change c i = c j at he
    rw [he]
    rcases bit_cases (c j) with hh | hh <;> simp [hh]
  have hn : w ≠ 0 := by
    intro he
    have hh := congrFun he i
    simp [w,supportWord] at hh
  have hmin := golay_minimum w hw hn
  have hwt : hammingNorm w = 2 := by
    have he : Finset.univ.filter (fun k => w k ≠ 0) = {i,j} := by
      ext k
      simp [w,supportWord]
      tauto
    change (Finset.univ.filter (fun k => w k ≠ 0)).card = 2
    rw [he,Finset.card_pair hij]
  omega

end Atlas.Conway
