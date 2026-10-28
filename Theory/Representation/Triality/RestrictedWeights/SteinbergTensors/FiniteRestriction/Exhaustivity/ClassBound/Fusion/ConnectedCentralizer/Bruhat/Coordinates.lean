module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Basic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Chain
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Product

/-!
# Assembly of positive-root coordinates in actual D4 geometry

For the explicit positive-root order, relative normalization of each tail gives
existence of an ordered product. Trivial intersection of each leading root with
its tail gives uniqueness. The one-parameter isomorphisms in `Geometry` turn
these subgroup factorizations into coordinates in the supplied parameters,
without a Chevalley compatibility condition on those parameters.

The geometric normalization and intersection inputs remain explicit here.
This is a conditional assembly of the pointwise part of Steinberg 6.2(b), not
an assertion that those inputs have been constructed from `Geometry`.

Source: `refs/KGroup/GLS3/Chapter2St2.tex`, 6.2(b), and
`refs/KGroup/GLS3/Chapter1.tex`, 1.12.7(a)--(c).
-/

public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup
namespace ConnectedCentralizer.Bruhat

universe u
variable {k : Type u} [Field k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

/-- Subgroup geometry supplies coordinates in the actual supplied root
parameters. The two geometric premises must be discharged independently. -/
theorem positiveCoordinates_of_tail_geometry (S : Geometry K)
    (hnormal : Coordinates.TailNormalizes S)
    (hdisjoint : Coordinates.TailDisjoint S) : Nonempty (PositiveCoordinates S) := by
  exact nonempty_toralRootCoordinates_of_suffixes S.roots S.rootParameter
    S.roots.positive (Coordinates.positiveOrder S)
    (Coordinates.positiveOrder_nodup S) (Coordinates.mem_positiveOrder S)
    hnormal hdisjoint

end ConnectedCentralizer.Bruhat
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
