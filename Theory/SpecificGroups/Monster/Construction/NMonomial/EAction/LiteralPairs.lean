module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.Forms

/-!
# The three literal pair families in a common axis notation

Axes zero, one, and two denote the existing off-diagonal matrix, `wPlus`,
and `wMinus` summands. This only indexes the published vectors: their
inclusions and source normalization are unchanged.

Source: Aschbacher, *Sporadic Groups*, 29.1(2) and 29.10(3), pp. 154, 159.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.EAction
open TrialitySpin.SignedModules.Natural Atlas.Codes

/-- The literal vectors to which the signed symmetric pair model must be compared. -/
def literalPair (i : Axis) (x y : Omega) (hxy : x ≠ y) : ESpace :=
  match i with
  | 0 => ePairOne x y hxy
  | 1 => ePairTwo x y hxy
  | 2 => ePairThree x y hxy

@[simp] theorem literalPair_zero (x y : Omega) (hxy : x ≠ y) :
    literalPair 0 x y hxy = ePairOne x y hxy := rfl

@[simp] theorem literalPair_one (x y : Omega) (hxy : x ≠ y) :
    literalPair 1 x y hxy = ePairTwo x y hxy := rfl

@[simp] theorem literalPair_two (x y : Omega) (hxy : x ≠ y) :
    literalPair 2 x y hxy = ePairThree x y hxy := rfl

/-- No rescaling is hidden in the short-family comparisons. -/
theorem literalPair_inclusion (i : Axis) (x y : Omega) (hxy : x ≠ y) :
    eInclusion (literalPair i x y hxy) =
      match i with
      | 0 => LocalC.symmetricInclusion LocalC.sourceLatticeComparison
          (pairMatrix (LocalC.coordinateMarking.symm x) (LocalC.coordinateMarking.symm y))
      | 1 => LocalC.shortInclusion LocalC.sourceLatticeComparison
          (LocalC.ShortFamilies.wPlus x y hxy)
      | 2 => LocalC.shortInclusion LocalC.sourceLatticeComparison
          (LocalC.ShortFamilies.wMinus x y hxy) := by
  fin_cases i
  · exact eInclusion_pairOne x y hxy
  · exact eInclusion_pairTwo x y hxy
  · exact eInclusion_pairThree x y hxy

end Sporadic.Monster.Construction.NMonomial.EAction
