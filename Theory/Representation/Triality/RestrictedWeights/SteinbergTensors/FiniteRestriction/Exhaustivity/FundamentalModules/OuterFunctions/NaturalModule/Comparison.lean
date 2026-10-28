module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalInput
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates

/-!
# The geometric comparison needed for the D4 natural module

This interface specifies a regular homomorphism from the supplied group to
actual Clifford Spin, matching the marked torus and positive root subgroups.
The torus parameters are evaluations of the four raw fundamental characters,
so matching preserves their integral exponents and the original numbering.
Neither a point-group equivalence nor an unrelated family name supplies this
interface. Its unconditional construction remains a separate obligation.

Source: the identification with Spin in GLS3 Example 1.14.9(d),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open D4RestrictedWeight
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Evaluate all four raw fundamental characters on an actual torus point. -/
def rawTorusCoordinates (S : Geometry K) (t : S.torus.carrierVariety.Point) : Fin 4 → kˣ :=
  fun i => torusPointEval S.torus.carrierVariety t (S.coordinateEmbedding (Pi.single i 1))

/-- A compatible regular map from the supplied group to the concrete Spin carrier.
The torus equation matches all four raw fundamental coordinates, and the root
condition uses the actual positive root subgroups. No representation or highest
vector is a field. Existence is a separate geometric theorem. -/
structure SpinComparison (S : Geometry K) where
  morphism : Theory.AlgebraicGroup.Morphism K (groupVariety k)
  torus : ∀ t : S.torus.carrierVariety.Point,
    morphism.onPoints (S.torus.includePoint t) =
      CorootTorus.parameter k (rawTorusCoordinates k S t)
  positive_root : ∀ r ∈ S.roots.positive,
    ∀ z : (S.roots.rootSubgroup r).carrierVariety.Point, ∃ a : k,
      morphism.onPoints ((S.roots.rootSubgroup r).includePoint z) =
        rootPoint k (S.rootIndex r) a

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
