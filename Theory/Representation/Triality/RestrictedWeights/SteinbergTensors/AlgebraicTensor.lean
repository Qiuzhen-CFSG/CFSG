module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.HighestWeights
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.Weights
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.ClassificationLeft
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights.Graph
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights.Coefficient

/-!
# Rational D4 Steinberg tensors and twist equivalences

For `RationalBasicFamily S.borel S.torus S.leftWeightEmbedding`, the specified
tensor products are rational irreducible and have highest weight
`∑ i < n, 2^i coefficient(a_i)` in actual left simple-coroot coordinates.
They exhaust rational irreducibles in the restricted range, with unique
length-`n` binary parameters and actual intertwining equivalences, including
`n = 1`. The geometric inputs retain the simple universal algebraic group,
realized D4 roots, torus characters and pinning. The raw highest-weight APIs
remain available separately.

The left graph and inverse-graph pullbacks use `diagramAction` and
`inverseDiagramAction`, respectively. Output coefficient Frobenius is
equivalent to ordinary geometric Frobenius pullback. All three transports
supply actual intertwiners. Finite-restriction classification and finite
character periods remain separate obligations.

Source: GLS3, Definitions 2.8.1/2.8.3, Theorem 2.8.5, the rational argument
in Corollary 2.8.6(a), and Remark 2.8.8, `refs/KGroup/GLS3/chapter2.tex`.
-/
