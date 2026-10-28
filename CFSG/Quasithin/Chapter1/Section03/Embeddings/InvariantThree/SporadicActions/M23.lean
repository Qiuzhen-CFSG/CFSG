module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M23.IntrinsicLine
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M23.TwoCoreCenter

/-!
# The invariant Frattini line for an M23 Sylow pair

The center of the two-core of the actual product RS is characteristic in RS.
The concrete four-set stabilizer calculation proves that this center has order
four. The intrinsic conjugation calculation then constructs an invariant subgroup
of order three in R/Φ(R), even for the full pair automizer. This proves
`m23_carrierPairExclusion` without an additional geometric or action premise.

The placement and center calculation use actual subgroups of the fixed
Witt-design carrier. The source local group is E₁₆ extended by ΓL₂(4), including
Frobenius; the intrinsic line construction retains all ambient automorphisms
preserving the pair and requires no splitting assertion for that extension.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Asc86b; GLS3, Table 5.3d.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
open Sporadic.Mathieu

/-- The actual two-core center supplies the characteristic subgroup used by
the intrinsic line construction. -/
public theorem m23_pairReducible_of_twoCore_center_card
    {S : Sylow 2 M23} {R : Subgroup M23} (h : PairInput S R)
    (hc : Nat.card (center (pCore 2 (R ⊔ (S : Subgroup M23) : Subgroup M23))) = 4) :
    PairReducible (S : Subgroup M23) R := by
  let X : Subgroup M23 := R ⊔ (S : Subgroup M23)
  let Z : Subgroup X := (center (pCore 2 X)).map (pCore 2 X).subtype
  have hZ : Nat.card Z = 4 :=
    (card_map_of_injective (pCore 2 X).subtype_injective).trans hc
  exact m23_pairReducible_of_characteristic_four h Z hZ

/-- Carrier assembly from the actual geometric calculation for every source pair. -/
public theorem m23_carrierPairExclusion_of_twoCore_center_card
    (hcenter : ∀ (S : Sylow 2 M23) (R : Subgroup M23), PairInput S R →
      Nat.card (center (pCore 2 (R ⊔ (S : Subgroup M23) : Subgroup M23))) = 4) :
    CarrierPairExclusion ClassificationModels.SporadicName.m23.Carrier := by
  intro _ _ _ S R h
  exact m23_pairReducible_of_twoCore_center_card h (hcenter S R h)

/-- Every two-subgroup of the actual M23 pair automizer preserves a proper
nonzero subgroup of the Frattini quotient. The concrete two-core-center
calculation discharges the invariant-line construction's geometric premise. -/
public theorem m23_carrierPairExclusion :
    CarrierPairExclusion ClassificationModels.SporadicName.m23.Carrier :=
  m23_carrierPairExclusion_of_twoCore_center_card
    (fun _ _ h => m23_pair_twoCore_center_card h)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
