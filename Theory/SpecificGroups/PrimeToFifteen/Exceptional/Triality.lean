module
public import Theory.SpecificGroups.PrimeToFifteen.Exceptional.RootPair
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRoots
/-!
# A cubic in every genuine triality carrier

The central D4 node is fixed by the pinned triality diagram. Its positive and
negative parameter-one roots are fixed by the graph-field map and are p-elements,
so both lie in the literal elementary fixed group. Their faithful matrix images
supply the rank-one braid relation and the noncentral cubic, which survives the
actual quotient by the center. The proof treats every field characteristic.

Source: the graph-field and elementary-group construction in GLS3 Sections
2.2–2.4, and the integral rank-one relations in Steinberg Section 3.
-/
public section
open Matrix RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
noncomputable section
namespace Triality.Standard.PrimeToFifteen
open Parabolics ElementaryCentralKernel
local instance : DecidableEq ((typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2+2)) :=
  fun a b => instDecidableEqSum a b

private def ambient (P : Parameters) :=
  (subgroup (typeDRootPairing_base 2) (ExtensionField P)).subtype.comp (elementaryInclusion P)

/-- The central simple root forces three-divisibility in every characteristic. -/
theorem three_dvd_card (P : Parameters) : 3 ∣ Nat.card (Carrier P) := by
  apply RootPairing.SimpleGeckGroup.ThreeDivisibility.three_dvd_center_quotient_of_injective
    (ambient P) (Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective))
    (typeDRootPairing_baseEquiv 2 1)
    (centralElementary P true 1 (map_one _))
    ((centralElementary P false 1 (map_one _))⁻¹)
  · rfl
  · rw [map_inv]
    exact negativeUnit_inv _ _
end Triality.Standard.PrimeToFifteen
