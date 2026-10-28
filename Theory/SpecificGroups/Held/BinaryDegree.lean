module

public import Theory.SpecificGroups.Held.InvertedSevenCenter
public import Theory.Representation.ExtraspecialInvertedCenterDegree

/-!
# A faithful binary degree bound for the actual Held carrier

Restriction to the certified extraspecial seven subgroup and its center-inverting
involution gives degree at least forty-two. This applies to every faithful finite
binary representation, without an irreducibility assumption. It is stronger than
the degree-twenty bound needed in G.7 and suffices for K.4's degree-thirty-six
window. Transport to a quasisimple central cover still requires an actual
isomorphism to Held; this theorem makes no assertion about such covers.

Source: Aschbacher–Smith, G.7.1(2) and D.2.11 for the representation argument,
with K.4, printed p.457, as consumer. The ATLAS word calculation and its
provenance are in `InvertedSevenCenter`.
-/

namespace Held.BinaryDegree

/-- Every faithful finite-dimensional binary representation of Held has degree
at least forty-two, using the literal extraspecial subgroup and inverter. -/
public theorem finrank_ge_fortyTwo
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) He V) (hf : Function.Injective ρ) :
    42 ≤ Module.finrank (ZMod 2) V := by
  let := InvertedSevenCenter.seven_isExtraspecial
  exact Representation.ExtraspecialInvertedCenterDegree.fortyTwo_le_finrank
    ρ hf OddCubeCandidates.seven OddCubeCandidates.card_seven
    InvertedSevenCenter.inverter InvertedSevenCenter.inverter_isInvolution
    InvertedSevenCenter.inverter_center

end Held.BinaryDegree
