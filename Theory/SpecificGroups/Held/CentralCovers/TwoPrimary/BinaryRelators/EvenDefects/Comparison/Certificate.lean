module

public meta import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.WordLiteral
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Certificate.Block027

/-!
# The two certified cubic-triangle word identities

Source: John Bray, ATLAS `HeG1-P1.M`, retained in `Held/Model/Source/`.
The producer supplies data only. All equality and tail checks run in the kernel.
-/

public section

namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Certificate
open Replay

open Data Theory.GroupTheory.CosetEnumeration

variable {E : Type*} [Group E] {z x y : E}

theorem cube (h : Normalized z x y) :
    eval (symbolValue x y) (held_word% "-1772,-1772,-1772") = (tails h).val 12 := by
  have hr := Block027.valid (Initials.valid h) 17222 (by decide)
  change eval (symbolValue x y) (held_word% "-1772,-1772,-1772") = 1 * (tails h).val 12 at hr
  exact hr.trans (one_mul _)

theorem triangle (h : Normalized z x y) :
    eval (symbolValue x y) (held_word% "-1772,-3,-1772,-3") = (tails h).val 4 := by
  have hr := Block027.valid (Initials.valid h) 17206 (by decide)
  change eval (symbolValue x y) (held_word% "-1772,-3,-1772,-3") = 1 * (tails h).val 4 at hr
  exact hr.trans (one_mul _)


end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Certificate
