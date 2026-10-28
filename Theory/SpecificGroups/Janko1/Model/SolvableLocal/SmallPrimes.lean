module

public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.SmallPrimes.Reduction
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.SmallPrimes.Involutions

/-!
# The small-prime normalizer bounds for the actual J₁ model

The centralizers of the chosen elements of orders three and five contain no
commuting distinct involutions. The normalizer action on each cyclic subgroup,
together with the elementary Sylow two-structure, therefore excludes a subgroup
of order eight in either normalizer. Sylow conjugacy transports both bounds to
all subgroups of the corresponding prime order.

These are the exact restrictions needed from the order-sixty normalizer entries
in GLS3 Table 5.3f for the solvable-overgroup argument of Aschbacher–Smith,
*The Classification of Quasithin Groups*, printed p.510. No table entry is used
as a hypothesis: the involution checks concern the concrete matrix group.
-/

namespace Janko1.LocalStructure
open SmallPrimes OrderCertificate

/-- Eight does not divide the normalizer order of any subgroup of order three. -/
public theorem primeNormalizerBound_three : PrimeNormalizerBound 3 := by
  apply primeNormalizerBound_of_involution_pairs (by decide)
    (by norm_num [card_model]) b orderOf_b
  exact involution_pair_three

/-- Eight does not divide the normalizer order of any subgroup of order five. -/
public theorem primeNormalizerBound_five : PrimeNormalizerBound 5 := by
  apply primeNormalizerBound_of_involution_pairs (by decide)
    (by norm_num [card_model]) (x * y) orderOf_five
  exact involution_pair_five

end Janko1.LocalStructure
