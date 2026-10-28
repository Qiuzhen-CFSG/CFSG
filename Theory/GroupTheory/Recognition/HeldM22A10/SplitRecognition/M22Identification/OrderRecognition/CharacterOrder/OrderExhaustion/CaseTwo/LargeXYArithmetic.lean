module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeConstraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeXYArithmetic.Checks

/-!
# Exhaustion when the first or second signed degree has large ratio

A large ratio bounds the absolute value of its selected signed degree.
The restriction congruences give finitely many selected rows, and degree
divisibility makes the nonzero Suzuki denominator divide a fixed integer
for each such row. Substitution of the degree relation then gives a quadratic
in the other degree. The proved solver includes linear cases and the sole
constant case, where positivity bounds that other degree. Kernel reduction
checks all these candidates while retaining every original row and cofactor
condition.

The two extra numerical alternatives are deliberately retained: their
exclusion uses the other actual characters, outside this integer system.
The parent order-recognition argument supplies those exclusions.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15, the omitted elimination for case (2).
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion

/-- Complete numerical exhaustion for a large ratio at either of the first two rows. -/
public theorem caseTwo_largeXY_candidates {g : ℕ} {x y z a b c : ℤ}
    (S : CaseTwoIntegerSystem g x y z a b c)
    (hr : (x.natAbs : ℤ) < 4*a^2 ∨ (y.natAbs : ℤ) < 4*b^2) :
    g = 443520 ∨ (g = 93824640 ∧ x = -358 ∧ y = 180) ∨ (a = 7 ∧ b = -2) := by
  have h : LargeXY.alternative g x y a b := by
    rcases hr with hx | hy
    · exact LargeXY.checkX_sound S hx LargeXY.largeX_checks
    · exact LargeXY.checkY_sound S hy LargeXY.largeY_checks
  unfold LargeXY.alternative at h
  exact_mod_cast h

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
