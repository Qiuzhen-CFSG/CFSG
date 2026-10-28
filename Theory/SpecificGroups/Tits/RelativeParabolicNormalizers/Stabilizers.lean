module

public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.FirstCentralizer
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.SecondNormalizer

/-!
# Intrinsic invariance of both Tits parabolics

The first parabolic is the full centralizer of r5. Substituting that
identification into the second-normalizer calculation identifies the second
parabolic with the normalizer of the Sylow subgroup's second center.
An automorphism preserving the Sylow subgroup fixes r5 and preserves its
characteristic second center, hence preserves both parabolics.

This module re-exports `first_stabilized` and proves `second_stabilized`
without any additional centralizer or normalizer hypotheses.

Source: Parrott (1972), pp.672,683–684; the invariant-parabolic step of
Aschbacher–Smith 2.3.9(7), printed p.526.
-/

namespace Tits.RelativeParabolicNormalizers

/-- The second parabolic is the full normalizer of the explicit second center. -/
public theorem second_eq_normalizer :
    ExceptionalParabolics.second =
      Subgroup.normalizer (secondCenter : Set Atlas1600Group) :=
  second_eq_normalizer_secondCenter first_eq_centralizer

/-- Preserving the marked Sylow subgroup intrinsically preserves the second parabolic. -/
public theorem second_stabilized (β : MulAut Atlas1600Group)
    (hβ : atlas1600SylowTwoSubgroup.map β.toMonoidHom = atlas1600SylowTwoSubgroup) :
    ExceptionalParabolics.second.map β.toMonoidHom = ExceptionalParabolics.second :=
  second_stabilized_of_characteristic_normalizer secondCenter_characteristic
    second_eq_normalizer β hβ

end Tits.RelativeParabolicNormalizers
