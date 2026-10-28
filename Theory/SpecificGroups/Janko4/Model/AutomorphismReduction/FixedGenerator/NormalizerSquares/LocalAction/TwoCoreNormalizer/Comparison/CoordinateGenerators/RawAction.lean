module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.QuotientAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Max2Bridge

/-!
# The word-basis action to be realized on the J₄ two-core quotient

The candidate basis consists of the twelve conjugates of the max2 seed listed
below, transported by the proved `Max2Bridge` conjugator. The saved calculation
uses right conjugation and row coordinates. We record its inverse transposes,
so that the required identities use left conjugation on column vectors.

`RawCoordinates` is an outstanding concrete certificate, not an assertion of
local structure. Its coordinates must be constructed on the actual O₂(C)/Z(O₂(C)),
including the identification of the seed normal closure with O₂(C).
The separate alignment calculation changes these generators and coordinates
to the fixed ATLAS `3M22d2G1-f2r12B0` pair.

Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. The max2 word provenance and its
conjugacy bridge are documented in `TwoCoreCentralizer.Max2Bridge`.
-/

@[expose] public section

open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison
namespace CoordinateGenerators

open TwoCoreLinearModel

/-- Inverse transpose of the candidate right-conjugation-by-X matrix. -/
def rawMatrixX : Matrix12 := fromRows
  ![3073, 2050, 3080, 3076, 1056, 1040, 2304, 2560, 2112, 2176, 1024, 2048]

/-- Inverse transpose of the candidate right-conjugation-by-Y matrix. -/
def rawMatrixY : Matrix12 := fromRows
  ![514, 260, 1, 16, 64, 640, 8, 1792, 2560, 256, 288, 768]

/-- The first new generator, as a word in any group. -/
def firstWord {G : Type*} [Group G] (x y : G) : G := (x * y) ^ 7

/-- The second new generator, with the conjugation convention written explicitly. -/
def secondWord {G : Type*} [Group G] (x y : G) : G :=
  (x * y * x)⁻¹ * ((x * y) ^ 3 * y * (x * y) ^ 2 * y * (x * y) ^ 2) ^ 3 *
    (x * y * x)

/-- Coordinates for the actual two-core quotient realizing the seed-word basis.
The basis words, before transport, are the conjugates of s=(XYXYY)^11 by
`1, y, yy, yyx, yyxy, yyxyx, yyxyy, yyxyxy, yyxyyx, yyxyxyx, yyxyxyy, yyxyyxy`.
No normal-closure or p-core identification is implicit in this record. -/
structure RawCoordinates where
  coordinates : Coordinates
  actionX : ∀ q, rawMatrixX *ᵥ vector coordinates q =
    vector coordinates (involutionTwoCoreAction TwoCoreCentralizerData.localX q)
  actionY : ∀ q, rawMatrixY *ᵥ vector coordinates q =
    vector coordinates (involutionTwoCoreAction TwoCoreCentralizerData.localY q)

end CoordinateGenerators
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison
