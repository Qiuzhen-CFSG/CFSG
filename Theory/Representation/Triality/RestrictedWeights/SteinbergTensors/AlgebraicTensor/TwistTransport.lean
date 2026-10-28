module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.TwistTransport.Coefficient
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.TwistTransport.Graph

/-!
# Actual Frobenius and graph intertwining equivalences for rational D4 factors

Coefficient Frobenius squares matrix entries in an arbitrary finite basis and
is equivalent to ordinary geometric Frobenius pullback. Forward and inverse
pinned graph pullbacks are equivalent to the corresponding forward and inverse
diagram factors. Each equivalence follows from rationality, irreducibility,
the computed actual highest weight, and proved uniqueness using the explicit
opposite-Borel big cell. All three are exported as `Representation.Equiv` values.

Source: GLS3, Definition 2.8.3 and Remarks 2.8.4 and 2.8.8,
`refs/KGroup/GLS3/chapter2.tex`.
-/
