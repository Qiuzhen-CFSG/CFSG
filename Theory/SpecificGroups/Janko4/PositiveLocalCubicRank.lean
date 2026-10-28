module

public import Theory.Quasithin.PositiveLocalRank
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow

/-!
# Positive two-local cubic rank in Janko four

The certified centralizer of the original involution generator has
order 21799895040. Three divides this literal two-local order.

This is the local contribution used with the independent ordinary-rank
bound in the nonnormal-component sieve of Aschbacher--Smith A.1.34 and A.3.8.
Source for the literal model witness: GLS3 Table 5.3i, printed p.270; the original matrix and max2 certificates.
-/

public section
open Subgroup Theory.Quasithin

namespace Janko4

theorem one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 Model := by
  apply one_le_twoLocalPrimeRank_of_dvd_involution_centralizer a orderOf_a
  rw [OuterReduction.OddIndex.modelCentralizer_card]
  decide
end Janko4
