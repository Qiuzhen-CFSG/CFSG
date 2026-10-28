module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.Comparison

/-!
# Point maps for the marked D4-to-Spin comparison

`RootwiseSpinHom` separates the point-group construction from global regularity.
It matches the actual torus in its four raw fundamental coordinates and sends
each actual root parametrization to a scalar reparametrization of the numbered
Clifford root curve. All roots are included so that both sides of the big cell
can be used to prove regularity. No regularity, bijectivity, representation or
highest vector is a field, and existence is not asserted here.

The root-image lemma passes from the chosen parametrizations to arbitrary
points of the actual root subgroups, using their algebraic isomorphisms with
the additive group. The scalar need not equal one or be specified in advance.

Source: the Spin identification in GLS3 Theorem 1.10.7(d) and Example 1.14.9(d),
`refs/KGroup/GLS3/Chapter1.tex`; root parametrizations in Steinberg (6.1),
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
open Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning

universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

namespace SpinComparisonExistence

/-- A point homomorphism with fixed raw torus coordinates and scalar transport
of all actual root curves. Its existence and global regularity are separate
proof obligations. -/
structure RootwiseSpinHom (S : Geometry K) where
  pointHom : Variety.Point K →* Points k
  torus : ∀ t : S.torus.carrierVariety.Point,
    pointHom (S.torus.includePoint t) =
      CorootTorus.parameter k (rawTorusCoordinates k S t)
  rootScale : S.roots.Root → k
  root : ∀ r a,
    pointHom ((S.roots.rootSubgroup r).includePoint ((S.rootParameter r).value a)) =
      rootPoint k (S.rootIndex r) (rootScale r * a)

variable {k}

/-- Root-curve transport controls every point of the actual root subgroup. -/
theorem RootwiseSpinHom.root_image {S : Geometry K} (C : RootwiseSpinHom k S)
    (r : S.roots.Root) (z : (S.roots.rootSubgroup r).carrierVariety.Point) :
    ∃ a : k, C.pointHom ((S.roots.rootSubgroup r).includePoint z) =
      rootPoint k (S.rootIndex r) a := by
  obtain ⟨x, hx⟩ := (S.rootParameter r).toMulEquiv.surjective z
  obtain ⟨a, rfl⟩ : ∃ a, kPlusPoint a = x :=
    ⟨_, kPlusPoint_coordinate x⟩
  refine ⟨C.rootScale r * a, ?_⟩
  rw [← hx]
  exact C.root r a

end SpinComparisonExistence
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
