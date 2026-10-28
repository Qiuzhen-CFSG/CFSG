module

public import Theory.Mathieu.SchurMultipliers
public import Theory.Mathieu.SchurMultipliers.OddLocalPartialInversion

/-!
# Compatibility import for the M₁₁ and M₂₃ partial-inversion source results

The mathematical proofs now live in `OddLocalPartialInversion`, below the
Mathieu multiplier assembly, so its model-specific children can reuse the
odd-kernel exclusions without an import cycle. All original theorem names
remain in `Sporadic.Mathieu.SchurMultipliers.PartialInversionSource`.

This compatibility module retains the original multiplier-root reexports
as well as the complete partial-inversion API.
-/
