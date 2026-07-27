import Mathlib
import Submission.ZStar.OddCore

/-!
# Helper wrappers (replaced by `Submission.ZStar.OddCore`)

The original `oddCore` definition with `sorry` proofs is replaced by wrappers
around the `Submission.ZStar.OddCore` module which uses `pPrimeCore 2 G` from the
FeitThompson infrastructure.
-/

namespace Submission.Helpers

open Submission.ZStar

/-- The odd core `O(G) = O_{2'}(G)`: the largest normal subgroup of odd order. -/
abbrev oddCore (G : Type*) [Group G] : Subgroup G := ZStar.oddCore G

/-- The odd core is normal in G. -/
theorem oddCore_normal (G : Type*) [Group G] : (oddCore G).Normal :=
  ZStar.oddCore_normal G

/-- The odd core has odd cardinality. -/
theorem oddCore_odd (G : Type*) [Group G] [Finite G] : Odd (Nat.card (oddCore G)) :=
  ZStar.oddCore_odd G

end Submission.Helpers
