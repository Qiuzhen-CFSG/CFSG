module

public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation.LiftPairing

/-!
# Two remaining calculations for the relative first-parabolic bound

Separate detection of the derived two-kernel in the quaternion-core
preimage from the finite invariant-pairing count. The first obligation
uses the order-six quotient and its cubic action; the second uses the
marked commuting-lift relation. Their proved conjunction gives exactly
`FirstParabolicLiftBound`, for any universe.

The propositions below specify obligations, not established facts.
`firstParabolicLiftBound_of_core_calculations` retains both premises.
Source: the local upper-bound calculation for Aschbacher–Smith I.1.3(1),
printed p.407; the embedded core and quotient are those of 14.2.21.
-/

namespace Sporadic.Mathieu.SchurMultipliers.M12Upper
open Subgroup M12SmallPair
universe u

/-- Detection of the full central derived two-kernel inside the lifted core.
This is a separate obligation from the finite pairing calculation. -/
@[expose] public def FirstParabolicCoreDerivedDetection : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (q : D →* firstParabolic),
    Function.Surjective q → q.ker ≤ center D → IsPGroup 2 q.ker →
    q.ker ⊓ _root_.commutator D ≤ ⁅corePreimage q,corePreimage q⁆

/-- The relative bound restricted to the literal quaternion-core preimage.
The marked commuting-lift hypothesis is essential. -/
@[expose] public def FirstParabolicCoreLiftBound : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (q : D →* firstParabolic),
    Function.Surjective q → q.ker ≤ center D → IsPGroup 2 q.ker →
    (∃ a b : D, (q a : M12) = v ∧ (q b : M12) = third ∧ Commute a b) →
    Nat.card (q.ker ⊓ ⁅corePreimage q,corePreimage q⁆ : Subgroup D) ≤ 2

/-- Final local assembly from derived-kernel detection and the core pairing count.
Neither of the two remaining calculations is assumed to have been proved. -/
public theorem firstParabolicLiftBound_of_core_calculations
    (hdetect : FirstParabolicCoreDerivedDetection.{u})
    (hcore : FirstParabolicCoreLiftBound.{u}) : FirstParabolicLiftBound.{u} := by
  intro D _ _ q hq hk hp hvt
  exact (card_le_of_le (le_inf inf_le_left (hdetect D q hq hk hp))).trans
    (hcore D q hq hk hp hvt)

end Sporadic.Mathieu.SchurMultipliers.M12Upper
