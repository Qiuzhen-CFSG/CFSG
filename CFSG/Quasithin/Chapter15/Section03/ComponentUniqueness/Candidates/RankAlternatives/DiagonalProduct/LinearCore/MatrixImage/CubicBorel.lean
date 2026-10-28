module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage
public import Theory.SpecificGroups.PSL3.CubicBorel

/-!
# Adapter for the concrete cubic Borel calculation

The intrinsic matrix calculation uses precisely the closure of the elements
of order three in the specified Sylow normalizer. This is the chapter's
`theta`, without a change to either matrix or to the Sylow subgroup.
The root generation, triangular torus comparison and transport from standard
coordinates are discharged by the intrinsic theorem. The final result has
no extra model or local-group premises.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final paragraph
of 15.3.37, printed p.1135, with A.3.18, printed pp.52--53.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage

/-- The remaining intrinsic torus calculation suffices for the exact chapter
interface. This is a conditional adapter, not the completed source assertion. -/
theorem cubicBorelGeneration_of_triangularComparison
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (he : Even n) (hF : Nat.card F = 2 ^ n)
    (hcompare : Matrix.PSL3.CubicBorel.TriangularCubicComparison F) :
    CubicBorelGeneration F :=
  Matrix.PSL3.CubicBorel.generation_of_triangularComparison F hn he hF hcompare

/-- The exact cubic Borel obligation for every finite binary field of positive
even degree, with no restriction on the three-part of its multiplicative group. -/
theorem cubicBorelGeneration (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (he : Even n) (hF : Nat.card F = 2 ^ n) :
    CubicBorelGeneration F :=
  Matrix.PSL3.CubicBorel.generation F hn he hF

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage
