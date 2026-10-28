/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.AmbientGolayEncoder
public import Theory.AtlasPort.OtherSporadic.Mathieu.AffineMonomial

/-!
# AffineEncoderTransform

The row encoder transforms under an affine monomial permutation by an explicit new
hexacode word and repetition mask. Expanding the Kleinian quadratic form and its polar
pairing proves the coordinate identity.

Source: `Atlas/Mathieu/AffineEncoderTransform.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

theorem letter_neg : ∀ u : K, -u = u := by decide

theorem qK_add (u v : K) : qK (u+v) = qK u + qK v + polar u v := by
  revert u v; decide

theorem polar_isometry_inv (L : KIsometry) (u v : K) :
    polar u (L.symm v) = polar (L u) v := by
  have h := L.map_polar u (L.symm v)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

def affineRepetition (t : HexWord) (g : Monomial HexIndex) (h : HexWord)
    (r : HexIndex → Bit) (ε : Bit) (i : HexIndex) : Bit :=
  r (g.perm.symm i) + polar (Monomial.act g h i) (t i) +
    ε * (qK (t i) + lastColumnBit (g.perm.symm i) + lastColumnBit i)

/-- Exact transformation of arbitrary ambient parameters; no code hypotheses occur. -/
theorem affine_encoder_transform (t : HexWord) (g : Monomial HexIndex) (h : HexWord)
    (r : HexIndex → Bit) (ε : Bit) :
    coordinatePermutation (affinePermutation t g) (rowEncoder h r ε) =
      rowEncoder (Monomial.act g h + ε • t) (affineRepetition t g h r ε) ε := by
  funext p
  rcases p with ⟨i,k⟩
  change rowEncoder h r ε (g.perm.symm i,
    rowLabel.symm ((g.localMap i).symm (rowLabel k - t i))) = _
  simp only [rowEncoder,rowLabel.apply_symm_apply,polar_isometry_inv,KIsometry.map_q,
    sub_eq_add_neg,letter_neg,qK_add,affineRepetition,Pi.add_apply,Pi.smul_apply,
    Monomial.act_apply,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
    smul_eq_mul,LinearEquiv.apply_symm_apply]
  rw [polar_symmetric (rowLabel k) (t i)]
  ring_nf
  simp

end Atlas.Codes
