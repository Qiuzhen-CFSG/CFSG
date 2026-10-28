module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.Normalization
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Elimination.Certificate

/-!
# Elimination of Held's sixth-power defect

The source-word replay proves two central constraints: `r0 * r6 = 1` and
`r0 * r5 * r6 = 1`. All defects are central involutions, so cancellation gives
`r5 = 1`. The separate comparison `r0 = r5` then eliminates the square defect
in the owning module. Every certificate input is a literal Schreier rewrite
of one of the seven source words, evaluated in the arbitrary target group.

Source: John Bray's ATLAS `HeG1-P1.M`, retained in `Held/Model/Source/`.
The discovery traces, incremental replay and checking measurements are
documented in `Elimination/source/README.md`. No presentation identification,
multiplier, splitting theorem or vanishing defect is assumed.
-/

namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects
open Comparison

/-- The normalized sixth-power relator is exact, in any target group. -/
public theorem sixth_defect_eq_one {E : Type*} [Group E] (z x y : E)
    (h : Normalized z x y) : relationWord x y 5 = 1 := by
  have ht := (tails h).mul 9 4
  change (tails h).val 13 = (tails h).val 9 * (tails h).val 4 at ht
  rw [Elimination.Certificate.tail_nine h, Elimination.Certificate.tail_thirteen h,
    one_mul] at ht
  simpa [tails, tailCenter, maskBit, centralDefect] using ht.symm

end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects
