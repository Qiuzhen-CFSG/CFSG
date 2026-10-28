module

public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Reduction
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Orbit

/-!
# The large-prime normalizer bounds for the actual J₁ model

The checked involution orbit excludes involutions in the centralizers of the
standard elements of orders 7, 11 and 19. Sylow conjugacy transports this to
all subgroups of those orders. The normalizer action on each cyclic subgroup
has odd kernel and image of order dividing p−1, proving the required bound.

This verifies the consequence of the normalizer entries 7·6, 11·10, 19·6 in
GLS3 Table 5.3f needed in the local argument on Aschbacher–Smith p.510. The
proof uses the concrete ATLAS model and its certified order, without assuming
those table entries or an identification based on the ambient order alone.
-/

namespace Janko1.LocalStructure
open LargePrimes OrderCertificate

/-- Eight does not divide the normalizer order of any subgroup of order seven. -/
public theorem primeNormalizerBound_seven : PrimeNormalizerBound 7 := by
  apply bound_of_no_commuting_involution (by decide)
    (by norm_num [card_model]) (by decide) (a * b) orderOf_ab
  exact no_involution_commutes_seven

/-- Eight does not divide the normalizer order of any subgroup of order eleven. -/
public theorem primeNormalizerBound_eleven : PrimeNormalizerBound 11 := by
  apply bound_of_no_commuting_involution (by decide)
    (by norm_num [card_model]) (by decide) (x * y ^ 2) orderOf_eleven
  exact no_involution_commutes_eleven

/-- Eight does not divide the normalizer order of any subgroup of order nineteen. -/
public theorem primeNormalizerBound_nineteen : PrimeNormalizerBound 19 := by
  apply bound_of_no_commuting_involution (by decide)
    (by norm_num [card_model]) (by decide) (a * b * a * b ^ 2) orderOf_abab_sq
  exact no_involution_commutes_nineteen

end Janko1.LocalStructure
