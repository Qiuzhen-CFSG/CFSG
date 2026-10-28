/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetRecovery

/-!
# SextetTransitivity

The distinguished-sextet stabilizer, and therefore the full Golay automorphism group,
acts transitively on coordinates. A monomial automorphism matches the column and a
hexacode translation matches the row.

Source: `Atlas/Mathieu/SextetTransitivity.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

theorem sextet_coordinate_transitive (x y : Omega) :
    ∃ s : SextetStabilizer, s.val.val x = y := by
  obtain ⟨g,hg⟩ := hexCoordinateHom_surjective (Equiv.swap x.1 y.1)
  have hp : g.val.perm x.1 = y.1 := by
    have h := DFunLike.congr_fun hg x.1
    exact h.trans (Equiv.swap_apply_left _ _)
  obtain ⟨t,ht⟩ := hexCoordinate_surjective y.1
    (rowLabel y.2 - g.val.localMap y.1 (rowLabel x.2))
  refine ⟨sextetAffineEquiv ⟨Multiplicative.ofAdd t,g⟩,?_⟩
  rw [sextetAffineEquiv_coordinates]
  change (g.val.perm x.1,rowLabel.symm
    (g.val.localMap (g.val.perm x.1) (rowLabel x.2) + t.val (g.val.perm x.1))) = y
  rw [hp]
  change t.val y.1 = _ at ht
  rw [ht,add_sub_cancel, rowLabel.symm_apply_apply]

theorem golay_coordinate_transitive (x y : Omega) :
    ∃ g : Mathieu24CodeModel, g.val x = y := by
  obtain ⟨s,hs⟩ := sextet_coordinate_transitive x y
  exact ⟨s.val,hs⟩

end Atlas.Codes
