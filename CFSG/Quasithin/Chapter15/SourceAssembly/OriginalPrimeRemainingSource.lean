module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalQuinticPrimeSource
public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalQuinticPrimeExclusionSource

/-!
# Theorem E after the original residual-order-fifteen exclusion

The original residual-order-fifteen branch is now contradictory. Both
remaining quintic duties concern the same literal marked residual of order
five. The broad original later-exclusion consumer is supplied internally;
all original source guards and the independent rank-two and 15.3.13 duties
are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Theorem E with only the original residual-order-five quintic duties
remaining, after supplying the actual order-fifteen contradiction. -/
theorem source_theoremE_of_original_prime_remaining_sources
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hrank : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      RankTwoResolver T Mc)
    (hnormalize : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalQuinticPrimeFullNormalizationAt T Mc)
    (hquintic : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalQuinticPrimeExclusionAt T Mc)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  exact source_theoremE_of_original_quintic_prime_sources hG T hmany hempty hrank
    hnormalize (fun Mc hu => original_quintic_exclusion_of_prime_residual
      hG T hmany hempty hu (hquintic Mc hu)) h13

end CFSG.Quasithin.Chapter15
