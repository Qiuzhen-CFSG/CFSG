module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Splitting.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Splitting.CellSeparation.NormalizerIntersection
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Splitting.CellSeparation.SolvableTori

/-!
# Separation of actual D4 Borel double cosets

Distinct cosets of the actual torus in its actual normalizer give disjoint
positive-Borel double cosets. Positive-root coordinates prove `B ∩ N(T) = T`;
conjugacy of maximal tori inside a solvable Borel intersection then proves the
double-coset assertion. This separates the Weyl indices themselves, before
any uniqueness argument for the factors within one cell.

Only `PositiveCoordinates` is needed in addition to `Geometry`. In particular,
the permitted normalizer realization, root transport and coverage premises
are unnecessary for separation. Their independent construction remains with
the owners of the full Bruhat parametrization.

Source: GLS3 1.11.3--1.11.5 and Steinberg 6.3(a),
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup
namespace ConnectedCentralizer.Bruhat.Splitting

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

/-- Actual Borel double cosets separate actual normalizer cosets modulo the
chosen torus. The coordinate premise is the separate theorem of Steinberg 6.2(b). -/
theorem cellSeparation_of_positiveCoordinates (S : Geometry K)
    (C : Bruhat.PositiveCoordinates S) : CellSeparation S :=
  CellSeparation.coset_separation S.bigCell.data.B S.torus
    S.bigCell.data.B_isBorel.solvable S.maximalTorus S.bigCell.torus_le_positive
    (borel_inf_normalizer S C)

end ConnectedCentralizer.Bruhat.Splitting
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
