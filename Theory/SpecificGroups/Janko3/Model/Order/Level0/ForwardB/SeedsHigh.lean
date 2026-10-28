module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.CycleData
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsHigh.Blocks
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsHigh.Checks0
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsHigh.Checks1
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsHigh.Checks2
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsHigh.Checks3
import Mathlib.Tactic.FinCases

/-!
# Upper seed transitions for the J3 B row

The short-block soundness checks and four batches of transition comparisons
certify every selected seed at or above representative 4714.  The resulting
theorem is consumed by the B-cycle reduction in `ForwardB.lean`.
Source: the ATLAS-derived J3 witnesses in `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB

open Theory.GroupTheory

/-- The certified upper seed transitions for the first B Schreier row. -/
public theorem seedStepsHigh : ∀ r : Fin 6156, Seed r → 4714 ≤ r.val →
    L0Gen 1 * L0Rep r = L0Rep (L0Act 1 r) *
      evalWord L1Gen (L0Factor 1 r) := by
  apply SeedsHigh.seedStepsHigh_of_checks SeedsHigh.blockSound
  apply SeedsHigh.checks_of_batches SeedsHigh.checkZero
  intro b i
  fin_cases b
  · exact SeedsHigh.checks0 i
  · exact SeedsHigh.checks1 i
  · exact SeedsHigh.checks2 i
  · exact SeedsHigh.checks3 i

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB
