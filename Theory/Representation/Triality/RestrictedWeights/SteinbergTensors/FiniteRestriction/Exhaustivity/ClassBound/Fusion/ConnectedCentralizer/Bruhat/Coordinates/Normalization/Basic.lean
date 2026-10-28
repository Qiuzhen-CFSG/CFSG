module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Basic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Chain

/-!
# The actual positive-root commutator containment obligation

The correction roots are positive integral combinations in the standard D4
root pairing, transported by the actual root-index equivalence of `Geometry`.
The containment statement concerns the actual closed root subgroups. It asks
only for subgroup containment, without fixing coefficients or parameters.

Its proof from `Geometry` is separate from the height and collection argument
in `Coordinates.Normalization`. This interface asserts no existence theorem.

Source: GLS3, Chapter 1, Theorem 1.12.7(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped commutatorElement

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
namespace ConnectedCentralizer.Bruhat
noncomputable section
universe u
variable {k : Type u} [Field k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

namespace Coordinates.Normalization

/-- Positive roots in the integral cone spanned by two actual roots. -/
@[expose] public def positiveCommutatorRoots (S : Geometry K) (a b : S.roots.Root) : Set S.roots.Root :=
  {c | c ∈ S.roots.positive ∧ ∃ i j : ℕ, 0 < i ∧ 0 < j ∧
    (typeDRootPairing 2).root (S.rootIndex c) =
      (i : ℝ) • (typeDRootPairing 2).root (S.rootIndex a) +
      (j : ℝ) • (typeDRootPairing 2).root (S.rootIndex b)}

/-- The subgroup-containment part of GLS3 1.12.7(b) for distinct positive roots.
This is a geometric proof obligation, with no chosen Chevalley parameters. -/
@[expose] public def PositiveCommutatorContainment (S : Geometry K) : Prop :=
  ∀ a ∈ S.roots.positive, ∀ b ∈ S.roots.positive, a ≠ b →
    ⁅(S.roots.rootSubgroup a).toSubgroup, (S.roots.rootSubgroup b).toSubgroup⁆ ≤
      RootSubgroupGenerated S.roots (positiveCommutatorRoots S a b)


end Coordinates.Normalization
end
end ConnectedCentralizer.Bruhat
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
