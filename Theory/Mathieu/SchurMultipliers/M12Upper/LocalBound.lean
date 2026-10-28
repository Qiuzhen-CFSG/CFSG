module

public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore

/-!
# The relative first-parabolic calculation for the M₁₂ multiplier

The remaining finite local calculation concerns the actual centralizer of z,
of order 192. It bounds the derived part of a central two-kernel when lifts
of the specified v and `third` commute. The extra relation is essential:
a bound of two for all central extensions of this parabolic is false.

`FirstParabolicLiftBound` specifies this proof obligation; it does not assert
it. `M12Upper.Fusion` proves the commuting-lift premise for every global M₁₂
central extension, and `M12Upper` connects the local bound to the global
kernel by central transfer across the odd index 495.
Source: Aschbacher–Smith I.1.3(1), printed p.407, citing GLS3 §6.1.
-/

namespace Sporadic.Mathieu.SchurMultipliers.M12Upper
open Subgroup M12SmallPair
universe u

/-- The relative local bound still to be established. The codomain and both
marked elements are from the actual twelve-point Mathieu model. -/
@[expose] public def FirstParabolicLiftBound : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (q : D →* firstParabolic),
    Function.Surjective q → q.ker ≤ center D → IsPGroup 2 q.ker →
    (∃ a b : D, (q a : M12) = v ∧ (q b : M12) = third ∧ Commute a b) →
    Nat.card (q.ker ⊓ _root_.commutator D : Subgroup D) ≤ 2

end Sporadic.Mathieu.SchurMultipliers.M12Upper
