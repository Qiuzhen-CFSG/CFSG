import Mathlib
import Submission.Helpers
import Submission.FeitThompson

namespace Submission

theorem feit_thompson {G : Type*} [Group G] [Finite G]
    (h : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_theorem
  exact h

end Submission
