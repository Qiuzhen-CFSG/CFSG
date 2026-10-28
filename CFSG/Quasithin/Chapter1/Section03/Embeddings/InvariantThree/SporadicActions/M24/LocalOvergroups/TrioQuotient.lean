module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups.Reduction
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineQuotient
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoverage
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts

/-!
# The standard M₂₄ trio quotient

The native Witt-design geometry gives every element of the standard trio
stabilizer an affine form with one common binary linear part. Forgetting
the translations defines a homomorphism to S₃ × SL₃(2). Native lifts of
the product generators prove surjectivity, and kernel elements are binary
translations, so each squares to the identity. Supplying both proved
coordinate inputs completes `standardTrioQuotient`.

Source: Aschbacher, *Sporadic Groups*, Chapter 7, Lemma 20.2, printed p.97;
GLS3, Table 5.3e, E₆₄.N(3B). Only the quotient assertion is needed here.
-/

public section

open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction

/-- Assemble the full product quotient from coverage and lifts of the
actual stabilizer's affine coordinates. -/
theorem standardTrioQuotient_of_affine_coordinates
    (hc : AffineCoverage) (hl : AffineLifts) : StandardTrioQuotient :=
  ⟨affineQuotient hc, affineQuotient_surjective hc hl,
    affineQuotient_kernel_isPGroup hc⟩

/-- The native standard-trio stabilizer surjects onto S₃ × SL₃(2) with
a two-group kernel, as required by the local-overgroup construction. -/
theorem standardTrioQuotient : StandardTrioQuotient :=
  standardTrioQuotient_of_affine_coordinates affineCoverage affineLifts

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction
