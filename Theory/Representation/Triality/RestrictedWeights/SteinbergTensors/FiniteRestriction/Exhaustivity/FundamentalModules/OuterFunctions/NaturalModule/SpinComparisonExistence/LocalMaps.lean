module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.Data
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.RegularProduct
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.CliffordCurves
public import Theory.AlgebraicGroup.Tori.Character.Tuple

/-!
# Regular maps on the marked torus and root curves

Evaluating the four actual fundamental characters gives a regular map from
the source torus to the split four-torus. Composing it with the regular Spin
coroot product gives exactly the torus formula required by `SpinComparison`.
Composing the explicit Clifford curves with additive scalar multiplication
gives the regular maps required on every root curve.

For any `RootwiseSpinHom`, these maps lift its restrictions to the source
torus and roots. Extending this local regularity to the whole group remains
a separate geometric obligation; no inverse to the Spin cover is used.

Source: GLS3 Theorem 1.12.1 and Example 1.14.9(d),
`refs/KGroup/GLS3/Chapter1.tex`; Steinberg (6.1)--(6.2),
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

/-- The regular map with the prescribed raw fundamental torus coordinates. -/
def torusMorphism (S : Geometry K) :
    Morphism S.torus.carrierVariety (groupVariety k) :=
  (CorootTorus.productOfRegularRoots k (cliffordRootMorphism k)
    (cliffordRootMorphism_kPlusPoint k)).comp
      (torusCharacterTupleMorphism S.torus.carrierVariety 4
        (fun i => S.coordinateEmbedding (Pi.single i 1)))

/-- The torus map uses the original raw coroot convention. -/
theorem torusMorphism_apply (S : Geometry K) (t : S.torus.carrierVariety.Point) :
    (torusMorphism k S).onPoints t =
      CorootTorus.parameter k (rawTorusCoordinates k S t) := by
  change (CorootTorus.productOfRegularRoots k (cliffordRootMorphism k)
    (cliffordRootMorphism_kPlusPoint k)).onPoints _ = _
  rw [CorootTorus.productOfRegularRoots_apply]
  rfl

/-- The regular Clifford root curve with an arbitrary scalar parameter change. -/
def rootMorphism (S : Geometry K) (r : S.roots.Root) (c : k) :
    Morphism (KPlus k) (groupVariety k) :=
  (cliffordRootMorphism k (S.rootIndex r)).comp (additiveScalarMorphism c)

/-- The regular root map preserves the actual root numbering. -/
theorem rootMorphism_apply (S : Geometry K) (r : S.roots.Root) (c a : k) :
    (rootMorphism k S r c).onPoints (kPlusPoint a) =
      rootPoint k (S.rootIndex r) (c * a) := by
  change (cliffordRootMorphism k (S.rootIndex r)).onPoints (kPlusPoint (c * a)) = _
  exact cliffordRootMorphism_kPlusPoint k (S.rootIndex r) (c * a)

variable {k}

/-- Every marked point homomorphism is regular on the actual source torus. -/
theorem RootwiseSpinHom.torus_lift {S : Geometry K} (C : RootwiseSpinHom k S) :
    (torusMorphism k S).onPoints = C.pointHom.comp S.torus.inclusion.onPoints := by
  ext t
  exact (torusMorphism_apply k S t).trans (C.torus t).symm

/-- Every marked point homomorphism is regular on each actual root curve. -/
theorem RootwiseSpinHom.root_lift {S : Geometry K} (C : RootwiseSpinHom k S)
    (r : S.roots.Root) :
    (rootMorphism k S r (C.rootScale r)).onPoints =
      C.pointHom.comp (((S.roots.rootSubgroup r).inclusion).comp
        (S.rootParameter r).hom).onPoints := by
  ext x
  obtain ⟨a, rfl⟩ : ∃ a, kPlusPoint a = x :=
    ⟨_, kPlusPoint_coordinate x⟩
  exact (rootMorphism_apply k S r (C.rootScale r) a).trans (C.root r a).symm

end SpinComparisonExistence
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
