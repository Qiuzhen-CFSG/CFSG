module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveLocal
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneOrbit

/-!
# The five-local geometry needed for binary degree fourteen

The remaining group calculation is an elementary abelian subgroup of order
25 whose actual ambient normalizer has no hyperplane orbit of length below
three. A fixed-point-free cubic normalizer on the five-plane supplies this:
an invariant line would give an order-three automorphism of a group of order
five, whose automorphism group has order four.

This is a group-theoretic contract, with no representation or dimension
assumptions. It is not yet a certificate for the degree-100 J₂ carrier.
The dimension argument is proved separately in `Dimension`.

Sources: the ATLAS J₂ subgroup 5²:D₁₂, and the restriction argument for the
degree-fourteen case of Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, manuscript p.16. The proposed cubic words are exploratory
data until their equations in the actual carrier have been checked in Lean.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
open Sporadic.LeechRelated.J2

/-- Sufficient local geometry in the actual carrier. The orbits use literal
conjugation by `N_Carrier(P)`, not the full abstract automorphism group of P. -/
@[expose] def FiveNormalizerGeometry : Prop :=
  ∃ P : Subgroup Carrier, Nat.card P = 25 ∧ IsElementaryAbelian 5 P ∧
    ∀ H : Subgroup P, H.index = 5 →
      3 ≤ Nat.card (BinaryCoprimeDegree.normalizerHyperplaneOrbit P H)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
