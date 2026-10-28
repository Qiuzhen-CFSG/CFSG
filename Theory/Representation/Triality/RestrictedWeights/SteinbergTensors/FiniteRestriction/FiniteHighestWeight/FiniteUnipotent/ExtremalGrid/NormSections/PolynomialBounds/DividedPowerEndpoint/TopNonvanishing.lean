module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.Operators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.RankOne
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.Charts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.WeylOrder

/-!
# Inputs for nonvanishing of the D4 top divided-power words

The rank-one endpoint is proved for every finite-dimensional rational module:
its degree-m coefficient is the actual Weyl translate of the highest vector.
The chart comparison transfers both signs to the supplied D4 parameters,
retaining the nonzero scalar changes. The Weyl-order calculation identifies
all twelve actual roots crossed by the opposition word.

Two further steps are needed for the literal top words: transport the rank-one
endpoints along the opposition word, and compare its convex operator order
with the supplied height order using truncated coefficient relations. This
module does not yet assert nonvanishing of either full twelve-root word.

Source: Steinberg, Representations of algebraic groups (1963), §§2.8 and 4.3;
GLS3 Chapter2St2.tex, 13.2(d). Corollary 8.3 concerns irreducible modules and
is not used to assert a basis theorem for arbitrary cyclic modules.
-/
