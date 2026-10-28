module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Scalar-invariant pairings and triple maps

These predicates express the two finite-field inputs to the Suzuki
central-defect argument. The input is the additive field, and invariance
means simultaneous multiplication of every argument by the same nonzero
field element. The codomain is an arbitrary commutative group; no action
on it is implicit. The predicates assert vanishing of all such pairings
and triple maps, not splitting of a covering group.

For binary fields of dimension at least four, the needed vanishing follows
from the absence of zero weights among sums of two or three Frobenius weights.
The exceptional field of eight elements has a nonzero invariant triple map.
-/

public section
namespace ScalarInvariantMaps
universe u v
variable (F : Type u) [Field F]

/-- Every biadditive scalar-invariant map to a commutative group vanishes. -/
@[expose] def PairingsVanish : Prop :=
  ∀ (C : Type v) [CommGroup C] (b : Multiplicative F →* (Multiplicative F →* C)),
    (∀ (t : Fˣ) x y,
      b (Multiplicative.ofAdd (t * x.toAdd)) (Multiplicative.ofAdd (t * y.toAdd)) = b x y) →
    b = 1

/-- Every triadditive scalar-invariant map to a commutative group vanishes. -/
@[expose] def TriplesVanish : Prop :=
  ∀ (C : Type v) [CommGroup C]
    (b : Multiplicative F →* (Multiplicative F →* (Multiplicative F →* C))),
    (∀ (t : Fˣ) x y z,
      b (Multiplicative.ofAdd (t * x.toAdd)) (Multiplicative.ofAdd (t * y.toAdd))
        (Multiplicative.ofAdd (t * z.toAdd)) = b x y z) →
    b = 1

end ScalarInvariantMaps
end
