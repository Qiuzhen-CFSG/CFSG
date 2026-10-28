/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/TetradParityConstant.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSextetSigns
/-!
Explicit sextet and tetrad isometries of the integral Leech lattice.
Coordinate identities and the retained lattice generators certify the isometry operations.

Source: Gerald Höhn, `Atlas/Conway/TetradParityConstant.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem constant_of_tetrad_parity (c : BinaryWord)
    (hc : ∀ T : Finset Omega, T.card = 4 → tetradSignParity c T = 0) :
    ∀ i j, c i = c j := by
  classical
  intro i j
  by_cases hij : i = j
  · exact congrArg c hij
  have hn : 3 ≤ (Finset.univ \ {i,j} : Finset Omega).card := by
    rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Finset.card_pair hij]
    decide
  obtain ⟨U,hU,hcard⟩ := Finset.exists_subset_card_eq hn
  have hi : i ∉ U := by
    intro h; have := Finset.mem_sdiff.mp (hU h); simp at this
  have hj : j ∉ U := by
    intro h; have := Finset.mem_sdiff.mp (hU h); simp at this
  have hci := hc (insert i U) (by rw [Finset.card_insert_of_notMem hi,hcard])
  have hcj := hc (insert j U) (by rw [Finset.card_insert_of_notMem hj,hcard])
  simp only [tetradSignParity,Finset.sum_coe_sort,Finset.sum_insert hi,Finset.sum_insert hj] at hci hcj
  exact add_right_cancel (hci.trans hcj.symm)

end Atlas.Conway
