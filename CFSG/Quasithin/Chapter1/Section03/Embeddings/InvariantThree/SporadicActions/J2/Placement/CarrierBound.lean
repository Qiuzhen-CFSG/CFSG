module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.Coverage

/-!
# A carrier bound for the J₂ double-coset sieve

The checked normal-form cover gives an injection of the actual ATLAS carrier
into 604800 indices, by choosing a normal form for each element. This is only
an upper bound; it assumes neither exact group order nor simplicity. It is
used to prove coverage once sufficiently many distinct Sylow cosets are found.

Source: the retained ATLAS degree-100 data and the checked Schreier transitions
in `GeneratorPair.SecondOrbits.Coverage`.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate

/-- Normal-form coverage bounds the carrier without an order certificate. -/
theorem card_carrier_le : Nat.card Carrier ≤ 604800 := by
  classical
  choose code hcode using normalForm_cover
  have hi : Function.Injective code := by
    intro x y hxy
    apply inclusion_injective
    rw [hcode x, hcode y, hxy]
  have hc := Nat.card_le_card_of_injective code hi
  simpa only [Index, Nat.card_prod, Nat.card_fin] using hc

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement
