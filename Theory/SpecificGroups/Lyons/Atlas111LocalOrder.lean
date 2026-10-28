module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIdentificationSetup
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Transfer of the G₂(5) order to the concrete Lyons local subgroup

An actual isomorphism with the split-octonion automorphism group transports its
cardinality to the subgroup specified by the ATLAS words. Specializing the G₂
order formula at five gives 5859000000. Both the isomorphism and the formula
are explicit premises here; the unconditional local order still requires
those independent certificates.

Source for the concrete subgroup: R. A. Wilson et al., ATLAS of Finite Group
Representations, https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/LyG1-max1W1 .
Original program and attribution: `Atlas111OrderSource/`.
-/

namespace Lyons.OrderCertificate

public instance fivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Transfer the G₂ order formula along a certified concrete identification. -/
public theorem card_localSubgroup_of_g2_equiv
    (e : localSubgroup ≃* Atlas.G2.Model (ZMod 5))
    (hcard : Nat.card (Atlas.G2.Model (ZMod 5)) =
      Nat.card (ZMod 5) ^ 6 * (Nat.card (ZMod 5) ^ 6 - 1) *
        (Nat.card (ZMod 5) ^ 2 - 1)) :
    Nat.card localSubgroup = 5859000000 := by
  rw [Nat.card_congr e.toEquiv, hcard, Nat.card_zmod]
  rfl

end Lyons.OrderCertificate
