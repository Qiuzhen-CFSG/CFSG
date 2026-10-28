module

public import Theory.Quasithin.PositiveLocalRank
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Representatives

/-!
# Positive two-local cubic rank in Rudvalis

The original generator b has order four, and the certified centralizer
of b² has order 245760. Three divides this literal two-local order.

This is the local contribution used with the independent ordinary-rank
bound in the nonnormal-component sieve of Aschbacher--Smith A.1.34 and A.3.8.
Source for the literal model witness: Aschbacher--Smith 16.1.5(11), printed p.1172; GLS3 Table 5.3r.
-/

public section
open Subgroup Theory.Quasithin

namespace Rudvalis

theorem one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 Model := by
  have ht : orderOf (b ^ 2) = 2 := by rw [orderOf_pow, orderOf_b]; decide
  apply one_le_twoLocalPrimeRank_of_dvd_involution_centralizer (b ^ 2) ht
  change 3 ∣ Nat.card (InvolutionCentralizers.Centralizer (b ^ 2))
  rw [InvolutionCentralizers.first_centralizer_card (IsConj.refl (b ^ 2))]
  decide
end Rudvalis
