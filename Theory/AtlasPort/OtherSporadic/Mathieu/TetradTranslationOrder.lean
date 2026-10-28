/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.TetradLocalNormal

/-!
# TetradTranslationOrder

The translation subgroup in either the affine or actual tetrad pointwise stabilizer has
order sixteen. The affine translation inclusion and the stabilizer equivalence transport
the cardinality of the one-zero hexacode module.

Source: `Atlas/Mathieu/TetradTranslationOrder.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

theorem tetradAffineTranslations_card (i : HexIndex) :
    Nat.card (tetradAffineTranslations i) = 16 := by
  have he := Nat.card_congr (MonoidHom.ofInjective
    (SemidirectProduct.inl_injective (φ := hexZeroAffineAction i))).toEquiv
  exact he.symm.trans (hexZeroCoordinate_card i)

theorem tetradPointTranslations_card (i : HexIndex) :
    Nat.card (tetradPointTranslations i) = 16 := by
  unfold tetradPointTranslations
  rw [← Nat.card_congr ((tetradAffineTranslations i).equivMapOfInjective
    (tetradPointStabilizerEquiv i).toMonoidHom
    (tetradPointStabilizerEquiv i).injective).toEquiv]
  exact tetradAffineTranslations_card i

end Atlas.Codes
