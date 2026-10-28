module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.Branches

/-!
# The two remaining coordinate calculations for the outside-C branch

The square calculation and the conjugation calculation have separate inputs.
The latter can be proved for arbitrary positive words whose first B₂ block
vanishes. The former then forces a normalized involution onto the explicit
five-parameter slice handled by `OutsideC.NormalForm`. These are specifications,
not assertions of either calculation or of involution classification.

Source: GLS3 Table 2.4 and 2.4.5(d), refs/KGroup/GLS3/chapter2.tex;
the involution-class input to Guralnick--Malle Lemma 8.8, internal p.57.
-/

@[expose] public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC
open NormalizedRootCentralizers.CenterExponent ElementaryTwoBound.RootCalculations

/-- Square-coordinate equations, before and after removing the two main parameters. -/
structure SquarePruning (m : ℕ) : Prop where
  initial : ∀ p : PositiveParameters m, p.pair 0 ≠ 0 → wordElement m p ^ 2 = 1 →
    p.main 0 = 0 ∧ p.central 0 = 0
  normalized : ∀ p : PositiveParameters m, p.pair 0 ≠ 0 → wordElement m p ^ 2 = 1 →
    p.main 0 = 0 → p.central 0 = 0 → p.main 2 = 0 → p.main 3 = 0 →
    p.main 1 = 0 ∧ p.pair 1 = 0 ∧ p.central 3 = 0

/-- Remove the X₇ and X₃ main parameters by actual conjugation, preserving X₈
and the absent X₁ block. No square or involution-class premise is required. -/
def MainNormalization (m : ℕ) : Prop :=
  ∀ p : PositiveParameters m, p.pair 0 ≠ 0 → p.main 0 = 0 → p.central 0 = 0 →
    ∃ q : PositiveParameters m,
      IsConj (wordElement m p) (wordElement m q) ∧
      q.pair 0 = p.pair 0 ∧ q.main 0 = 0 ∧ q.central 0 = 0 ∧
      q.main 2 = 0 ∧ q.main 3 = 0

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC
