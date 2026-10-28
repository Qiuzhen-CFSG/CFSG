module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineQuotient
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.Generation

/-!
# Lifting the full product of trio coordinates to native M₂₄

Every element of S₃ × SL₃(2) is a product of the four coordinate generators.
Each generator has a checked lift preserving the native Golay code and the
standard trio. Composing their affine formulas constructs a lift for every
element of the product; the translations compose along with the linear parts.

This proves the lift obligation in the trio quotient construction. It does
not need affine coverage of the stabilizer or a choice of a splitting.

Source context: Aschbacher, *Sporadic Groups*, Chapter 7, Lemma 20.2(2),
printed p.97; GLS3, Table 5.3e, E₆₄.N(3B).
-/

public section

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction

open AffineLiftConstruction

/-- Every octad permutation and common binary special linear part has an
actual lift in the native M₂₄ stabilizer of the standard trio. -/
theorem affineLifts : AffineLifts := by
  intro q
  apply quotient_induction (fun q => ∃ g t, HasAffineForm g q t) ?_ ?_ ?_ q
  · exact ⟨1, 0, hasAffineForm_one⟩
  · rintro a b ⟨g, t, hg⟩ ⟨h, u, hh⟩
    exact ⟨g * h, _, hasAffineForm_mul hg hh⟩
  · intro k
    exact ⟨generatorLift k, generatorTranslation k, generatorLift_hasAffineForm k⟩

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
