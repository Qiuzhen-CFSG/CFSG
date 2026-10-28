module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveLocal
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveFixedSpace.Dimension
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveFixedSpace.Normalizer

/-!
# The five-local fixed-space calculation for the actual J₂ carrier

The checked normalizer geometry supplies an elementary abelian subgroup of
order 25 with hyperplane orbits of length at least three. These orbits force
at least twelve moved dimensions, and binary five-group divisibility makes the
remaining fixed dimension exactly two. Combining the concrete geometry with
the dimension argument proves the fixed-space contract without extra premises.

This supplies precisely the `FiveFixedSpaceTwo` interface used by the descended
binary model in `FourteenTraceSeparation`, without absolute irreducibility.

Source: the ATLAS 5²:D₁₂ subgroup and Guralnick--Malle, Classification of
2F-modules I, Proposition 5.1, manuscript p.16.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow

/-- The concrete local geometry discharges the entire fixed-space contract. -/
theorem fiveFixedSpaceTwo_of_normalizerGeometry (hgeometry : FiveNormalizerGeometry) :
    FiveFixedSpaceTwo := by
  obtain ⟨P, hP, habelian, horbit⟩ := hgeometry
  let := habelian
  refine ⟨P, hP, fun σ hf => ?_⟩
  exact BinaryCoprimeDegree.finrank_invariants_eq_two_of_five_orbits σ hf
    (by simp) P hP horbit

/-- The actual Hall–Janko carrier has an order-25 subgroup fixing precisely
two dimensions in every faithful binary fourteen-dimensional representation. -/
theorem fiveFixedSpaceTwo : FiveFixedSpaceTwo :=
  fiveFixedSpaceTwo_of_normalizerGeometry fiveNormalizerGeometry

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
