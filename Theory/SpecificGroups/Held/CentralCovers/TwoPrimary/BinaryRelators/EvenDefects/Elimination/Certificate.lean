module

public meta import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.WordLiteral
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Elimination.Certificate.Block022

/-!
# Two central constraints eliminating the common even defect

Source: John Bray, ATLAS `HeG1-P1.M`, retained in `Held/Model/Source/`.
The producer supplies data only. All equality and tail checks run in the kernel.
-/

public section

namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Elimination.Certificate
open Comparison Comparison.Replay

open Theory.GroupTheory.CosetEnumeration

variable {E : Type*} [Group E] {z x y : E}

theorem tail_nine (h : Normalized z x y) : (tails h).val 9 = 1 := by
  have hr := Block022.valid (Initials.valid h) 28974 (by decide)
  change eval (symbolValue x y) (held_word% "1972,-1772,-688") =
    eval (symbolValue x y) (held_word% "1972,-1772,-688") * (tails h).val 9 at hr
  exact mul_left_cancel (hr.symm.trans (mul_one _).symm)

theorem tail_thirteen (h : Normalized z x y) : (tails h).val 13 = 1 := by
  have hr := Block022.valid (Initials.valid h) 29039 (by decide)
  change eval (symbolValue x y) (held_word% "3,-480,1772,2,23") =
    eval (symbolValue x y) (held_word% "3,-480,1772,2,23") * (tails h).val 13 at hr
  exact mul_left_cancel (hr.symm.trans (mul_one _).symm)


end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Elimination.Certificate
