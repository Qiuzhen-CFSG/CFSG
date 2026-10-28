module

public import Theory.Quasithin.PositiveLocalRank
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB
public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.Identities

/-!
# Positive two-local cubic rank in Held

The literal max5 subgroup has certified order 21504 and centralizes
its specified nonidentity involution. Divisibility of the actual centralizer
order by three supplies a local cubic witness.

This is the local contribution used with the independent ordinary-rank
bound in the nonnormal-component sieve of Aschbacher--Smith A.1.34 and A.3.8.
Source for the literal model witness: GLS3 Table 5.3p; the unchanged ATLAS HeG1-max5W1 certificates.
-/

public section
open Subgroup Theory.Quasithin

namespace Held
open TwoLocalCandidates

theorem one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 He := by
  apply one_le_twoLocalPrimeRank_of_dvd_involution_centralizer (max5First ^ 4)
    CentralInvolutionBounds.orderOf_centralInvolution
  have hd : Nat.card max5 ∣ Nat.card (centralizer ({max5First ^ 4} : Set He)) :=
    card_dvd_of_injective (inclusion CentralInvolutionBounds.max5_le_centralizer)
      (inclusion_injective _)
  apply dvd_trans (b := Nat.card max5) _ hd
  rw [InvolutionFixedData.TwoB.max5_card]
  decide
end Held
