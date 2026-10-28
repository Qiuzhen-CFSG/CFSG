/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetTransitivity
public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodeZeroCoordinate

/-!
# SextetTwoPointTransport

The sextet stabilizer realizes a prescribed column permutation and matches two marked
coordinates in distinct columns. Surjectivity of the monomial coordinate action and two-
coordinate hexacode projection determine the required affine map.

Source: `Atlas/Mathieu/SextetTwoPointTransport.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

theorem sextet_two_point_transport (σ : Equiv.Perm HexIndex) (a b c d : Omega)
    (hcd : c.1 ≠ d.1) (ha : σ a.1 = c.1) (hb : σ b.1 = d.1) :
    ∃ s : SextetStabilizer, (∀ i k, (s.val.val (i,k)).1 = σ i) ∧
      s.val.val a = c ∧ s.val.val b = d := by
  obtain ⟨g,hg⟩ := hexCoordinateHom_surjective σ
  have hp : ∀ i, g.val.perm i = σ i := fun i => DFunLike.congr_fun hg i
  obtain ⟨t,htc,htd⟩ := hex_two_values c.1 d.1 hcd
    (rowLabel c.2 - g.val.localMap c.1 (rowLabel a.2))
    (rowLabel d.2 - g.val.localMap d.1 (rowLabel b.2))
  refine ⟨sextetAffineEquiv ⟨Multiplicative.ofAdd t,g⟩,?_,?_,?_⟩
  · intro i k
    rw [sextetAffineEquiv_coordinates]
    exact hp i
  · change (g.val.perm a.1,rowLabel.symm
      (g.val.localMap (g.val.perm a.1) (rowLabel a.2)+t.val (g.val.perm a.1))) = c
    rw [hp,ha,htc,add_sub_cancel,rowLabel.symm_apply_apply]
  · change (g.val.perm b.1,rowLabel.symm
      (g.val.localMap (g.val.perm b.1) (rowLabel b.2)+t.val (g.val.perm b.1))) = d
    rw [hp,hb,htd,add_sub_cancel,rowLabel.symm_apply_apply]

end Atlas.Codes
