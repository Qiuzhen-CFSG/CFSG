module
public import Theory.SpecificGroups.PrimeToFifteen.Exceptional.RootPair
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.E6Twisting
/-!
# A cubic in the genuine twisted E6 central quotient

The diagram-fixed simple node 2 supplies both opposite root elements inside
 the defining-characteristic subgroup. Its faithful ambient matrix map lets
 the uniform root-pair criterion descend through the exact central quotient.
No folded F4 identification or odd-field rank-one embedding is needed.
Source: the pinned graph-field construction in GLS3 Sections 2.2–2.4.
-/
public section
open Matrix RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
noncomputable section
namespace TwistedE6
open FoldedSubsystem
attribute [local instance] Classical.decEq
theorem model_three_dvd_card (p m : ℕ) [Fact p.Prime] : 3 ∣ Nat.card (Model p m) := by
  apply RootPairing.SimpleGeckGroup.ThreeDivisibility.three_dvd_center_quotient_of_injective
    (ambientInclusion p m) (ambientInclusion_injective p m) (simpleIndex 2)
    (foldedRoot p m true 2 1) (foldedRoot p m false 2 (-1))
  · change (simpleRoot (CoefficientField p m) true 2 1).val = _
    exact simpleRoot_val _ true 2 1
  · change (simpleRoot (CoefficientField p m) false 2 (-1)).val = _
    exact simpleRoot_val _ false 2 (-1)
end TwistedE6
