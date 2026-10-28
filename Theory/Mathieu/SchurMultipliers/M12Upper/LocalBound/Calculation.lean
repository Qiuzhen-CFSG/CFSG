module

public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation.Reduction
public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation.CorePairingBound
public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation.DerivedDetection

/-!
# Relative first-parabolic calculation for M₁₂

For a finite central two-extension of the actual first parabolic, cubic
transfer detects the derived kernel in the derived subgroup of the literal
quaternion-core preimage. Its invariant binary commutator pairing, together
with the marked commuting-lift relation, bounds that kernel intersection
by two. Combining these results proves `FirstParabolicLiftBound` in every
universe, without a perfectness assumption on the extension group.

This supplies the local premise of
`m12_cover_kernel_card_le_two_of_firstParabolic_bound` in `M12Upper`.

Source: Aschbacher–Smith I.1.3(1), printed p.407, citing GLS3 §6.1.
The concrete parabolic geometry is that of 14.2.21, printed p.988.
-/

namespace Sporadic.Mathieu.SchurMultipliers.M12Upper
universe u

/-- A central two-extension of the first parabolic with commuting lifts of
the marked `v` and `third` has derived kernel of order at most two. -/
public theorem firstParabolicLiftBound : FirstParabolicLiftBound.{u} :=
  firstParabolicLiftBound_of_core_calculations
    firstParabolicCoreDerivedDetection firstParabolicCoreLiftBound

end Sporadic.Mathieu.SchurMultipliers.M12Upper
