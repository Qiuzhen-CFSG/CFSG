module
public import Theory.Quasithin.PositiveLocalRank
public import Theory.Quasithin.LocalRankEmbedding
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.Locality
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders
public import Theory.SpecificGroups.Tits.FiniteSimple

/-!
# Positive local cubic rank in the actual Tits carriers

The second Parrott parabolic is the normalizer of a specified nontrivial
two-subgroup and has order 6144. Cauchy's theorem supplies its cubic, giving
positive local three-rank. The marked Parrott-to-Atlas equivalence transfers
the witness back to the original presentation carrier.

Source: Aschbacher–Smith A.3.8 and F.1.12(I)(9), printed pp.45–46 and 263;
the genuine local subgroup and its order retain their Parrott references.
-/

public noncomputable section
namespace Tits

/-- The genuine second parabolic has order divisible by three and is two-local. -/
theorem atlas_one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 Atlas1600Group := by
  apply Theory.Quasithin.one_le_twoLocalPrimeRank_of_dvd_card
    ExceptionalParabolics.second ConverseLocalCoverage.second_isTwoLocal
  rw [ExceptionalParabolics.second_card]
  decide

/-- The local cubic witness on the original Parrott presentation carrier. -/
theorem parrott_one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 ParrottGroup :=
  atlas_one_le_twoLocalPrimeRank_three.trans (twoLocalPrimeRank_le_of_injective 3
    parrottFiniteImageEquiv.symm.toMonoidHom parrottFiniteImageEquiv.symm.injective)
end Tits

