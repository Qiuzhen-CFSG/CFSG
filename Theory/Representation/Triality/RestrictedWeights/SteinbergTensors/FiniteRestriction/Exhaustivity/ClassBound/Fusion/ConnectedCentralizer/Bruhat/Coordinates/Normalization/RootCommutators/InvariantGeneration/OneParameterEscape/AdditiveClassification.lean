module

public import Theory.AlgebraicGroup.Unipotent.OneParameterCore
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.InvariantGeneration.OneParameterEscape.AdditiveClassification.CoordinateHopf
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.InvariantGeneration.OneParameterEscape.AdditiveClassification.PolynomialCoordinate

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.InvariantGeneration.OneParameterEscape.AdditiveClassification.NormalRecovery

/-!
# Additive parametrizations of connected unipotent curves

Over an algebraically closed field of characteristic two, every connected
one-dimensional unipotent algebraic group is isomorphic to the additive group.

The actual coordinate Hopf algebra is a normal finite-type domain of
transcendence degree one and has a transcendental primitive element. The
positive-characteristic Hopf-curve argument proves rationality of its fraction
field. Translations and the one-pole theorem give a fraction parameter, and
normality recovers a polynomial generator in the original affine ring.
Normalizing this coordinate at the identity then yields the additive law and
an algebraic-group isomorphism, including its regular inverse.

Sources: GLS3, Definition 1.3.4 and Proposition 1.3.5(c); Borel, Theorem 10.9
and the algebraic sketch after Corollary 11.6. The finite-kernel additive
character supplies a primitive coordinate, without requiring a regular section.
-/

namespace Theory.AlgebraicGroup

universe u

/-- The characteristic-two converse of GLS Proposition 1.3.5(c). -/
public theorem connectedUnipotentCurve_isOneParameter_charTwo
    {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
    {Y : Variety k} [AlgebraicGroup Y]
    (hc : Variety.IsConnected Y) (hd : Variety.dimension Y = 1)
    (hu : IsUnipotentAlgebraicGroup Y) : IsOneParameterGroup Y := by
  let : HopfAlgebra k (Variety.PolynomialFunction Y) := coordinateHopfAlgebra Y
  let : IsDomain (coordinateRing Y) :=
    isDomain_coordinateRing_of_isIrreducible Y
      (connectedAlgebraicGroup_irreducible Y hc)
  let : IsDomain (Variety.PolynomialFunction Y) :=
    (coordinateRingAlgEquivPolynomialFunction Y).toRingEquiv.isDomain_iff.mp
      inferInstance
  let : Algebra.FiniteType k (Variety.PolynomialFunction Y) :=
    polynomialFunction_finiteType Y
  let : IsIntegrallyClosed (Variety.PolynomialFunction Y) :=
    AdditiveClassification.coordinate_normal_of_connected_curve Y hc hd
  have htrdeg := AdditiveClassification.coordinate_trdeg_of_connected_curve Y hc hd
  obtain ⟨t, ht, hprim⟩ :=
    AdditiveClassification.exists_transcendental_primitive_coordinate Y hc hd hu
  obtain ⟨s, hs, hgen⟩ :=
    AdditiveClassification.normal_primitive_hopf_curve_exists_affine_parameter_of_charP
      (p := 2) htrdeg t ht hprim
  exact AdditiveClassification.isOneParameter_of_polynomial_coordinate s hs hgen
end Theory.AlgebraicGroup
