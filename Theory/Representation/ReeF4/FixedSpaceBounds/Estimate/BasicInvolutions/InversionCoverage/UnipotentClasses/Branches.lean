module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.Contracts
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Curves

/-!
# The two coordinate branches of positive Ree involution coverage

The eighth paired parameter splits the positive subgroup into two cases.
When it vanishes, the endpoint square calculation places an involution in
the literal subgroup D = Y₁X₂X₃X₄X₅X₆Y₇. Otherwise a separate conjugacy
calculation is needed. These predicates specify those two calculations and
the existing endpoint-square interface; they assert none of them.

The ambient conjugacy is always in the actual exceptional-twist fixed model.
The assembly remains in `UnipotentClasses`.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8,
internal p.57. Coordinates and the subgroup D follow GLS3, Table 2.4,
2.4.5(d), and the first paragraph of the proof of Lemma 3.3.9.
-/

@[expose] public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
open EvenInvolutionGeometry ElementaryTwoBound
open ElementaryTwoBound.RootCalculations NormalizedRootCentralizers.CenterExponent

/-- The conjugacy calculation for a nonzero eighth paired coordinate. -/
def OutsideCConjugacy (m : ℕ) : Prop :=
  ∀ p : PositiveParameters m, p.pair 0 ≠ 0 → wordElement m p ^ 2 = 1 →
    IsLongRootInvolution (wordElement m p) ∨ IsShortRootInvolution (wordElement m p)

/-- The remaining conjugacy calculation in the actual nine-parameter subgroup. -/
def DConjugacy (m : ℕ) : Prop :=
  ∀ x : Model m, x ∈ D m → x ≠ 1 → x ^ 2 = 1 →
    IsLongRootInvolution x ∨ IsShortRootInvolution x

/-- The endpoint-square interface owned by
`ElementaryTwoBound.Replacement.EndpointSquares`. The eighth-coordinate
equation is explicit, so no subgroup-coordinate characterization is needed. -/
def EndpointSquareSupport (m : ℕ) : Prop :=
  ∀ p : PositiveParameters m, p.pair 0 = 0 →
    ∀ x : Model m, toSplitGroup m x = positiveWord m p → x ^ 2 = 1 → x ∈ D m

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
