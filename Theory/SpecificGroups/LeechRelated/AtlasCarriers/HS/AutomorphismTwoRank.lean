module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex
public import Theory.GroupTheory.PrimeRankAutomorphismOrder

/-!
# Automorphism two-rank of the exact HS carrier

Every automorphism is induced by an element of the permutation normalizer.
The quotient of that normalizer by HS therefore surjects onto Out(HS), whose
order divides two by the proved relative-index bound. Centerlessness identifies
the inner group with HS. The intrinsic rank bound four then gives automorphism
rank at most five, with no coverage or numerical premise.

Source: Aschbacher--Smith, G.7.3(2), printed p.348 (PDF p.359); GLS3,
Table 5.3m, printed p.274. All groups use the degree-100 ATLAS carrier.
-/

public section
namespace Sporadic.LeechRelated.HS
open Subgroup Theory.GroupTheory

/-- The actual outer automorphism group has order dividing two. -/
theorem outer_card_dvd_two : Nat.card (MulAut.Outer Carrier) ∣ 2 := by
  have hs := generated.normalizerOuterHom_surjective
    (normalizer_surjective_of_pointStabilizer_map pointStabilizer_map)
  have hd := Subgroup.card_dvd_of_surjective generated.normalizerOuterHom hs
  have hi : Nat.card (MulAut.Outer Carrier) ∣
      generated.relIndex (normalizer (generated : Set (Equiv.Perm (Fin 100)))) := by
    simpa only [relIndex, ← index_eq_card] using hd
  exact hi.trans normalizer_relIndex_dvd_two

/-- The automorphism two-rank bound required for the discarded HS case of G.7.3(2). -/
theorem automorphism_twoRank_le_five : primeRank 2 (MulAut Carrier) ≤ 5 := by
  have houter : Nat.card (MulAut.Outer Carrier) ≤ 2 ^ 1 :=
    Nat.le_of_dvd (by decide) outer_card_dvd_two
  exact (automorphism_primeRank_le_add_of_outer_card
    BlockNormalizer.center_carrier_eq_bot houter).trans
      (Nat.add_le_add_right twoRank_le_four 1)

end Sporadic.LeechRelated.HS
