module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer

/-!
# Applying the finite-presentation certificate to the literal local J₂ kernel

This discharges the finite-order premises in the parent's exact universal
projection bound. The parent retains ownership of its final public export.
Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407/PDF p.418.
-/

public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
open PerfectCentralCovering
open Sporadic.LeechRelated.J2.ExceptionalParabolics

/-- The certificate supplies the local order bound used in the J₂ multiplier proof. -/
theorem certified_local_universal_kernel_card_le_two :
    Nat.card (universalProjection Seed.l₁).ker ≤ 2 :=
  local_universal_kernel_card_le_two_of_presentation_bound
    presentation_finite_card_le.1 presentation_finite_card_le.2

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
