module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteTorusGeometry.Centralizers
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport
/-!
# Odd-class fusion and the finite triality class bound

The actual Frobenius has zero differential: it squares the torus, and the
torus and root tangents span. Connected odd centralizers therefore satisfy
Lang's theorem. The native fixed-point comparison identifies the elementary
subgroup with the whole fixed group, giving at most q⁴ odd-order classes.
All pinning, fusion and generation inputs are discharged on the original
Spin carrier; universality remains the shared algebraic source hypothesis.
Source: Steinberg 8.5, 10.1, 12.5 and 14.8; GLS3 2.8.2.
-/
public section
open Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction ClassBound
noncomputable section
namespace Triality.RestrictedWeights.Concrete.TorusGeometrySource
universe u
variable (k:Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu:IsUniversalVersion (groupVariety k))

theorem frobenius_differential_zero :
    Bor1.identityTangentMorphismLinearMap (finiteGeometry k hu).frobenius=0 := by
  apply Geometry.frobenius_differential_eq_zero_of_torus_square_of_tangent_span
  · intro t
    let S := finiteGeometry k hu
    let := S.torus.carrierAlgebraicGroup
    let F := Classical.choice (AmbientCount.TorusGeometry.nonempty_pinnedTorusMaps S)
    have he : F.frobenius.onPoints t=t^2 := by
      apply ConnectedCentralizer.Normalizer.torusPoint_ext S
      intro a
      rw [F.frobenius_weight]
      exact (map_pow _ t 2).symm
    exact (F.frobenius_ambient t).symm.trans (congrArg S.torus.includePoint he)
  · change LinearMap.range (Bor1.identityTangentMorphismLinearMap (CorootTorus.closedSubgroup k).inclusion) ⊔
      (⨆ a : ULift RootIndex, LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (rootClosedSubgroup k a.down).inclusion)) = ⊤
    simpa only [iSup_ulift] using torus_root_tangent_span k

theorem elementary_eq_top (n:ℕ) (hn:0<n) :
    graphFieldElementarySubgroup (finiteGeometry k hu).diagram.toMulEquiv
      (finiteGeometry k hu).frobenius.onPoints n=⊤ := by
  have he := Theory.GroupTheory.FixedElementary.map_powClosure 2 (Standard.binarySpinFixedEquiv k n hn)
  change (Standard.elementarySubgroup (Standard.binaryParameters n hn)).map
    (Standard.binarySpinFixedEquiv k n hn).toMonoidHom=GraphField.elementarySubgroup k n at he
  rw [Standard.ConcreteBruhat.FixedDescent.elementarySubgroup_eq_top_binary n hn,Subgroup.map_top_of_surjective _ (Standard.binarySpinFixedEquiv k n hn).surjective] at he
  have hh := GraphField.map_elementarySubgroup_orientation k n
  rw [←he,Subgroup.map_top_of_surjective _ (GraphField.orientationFixedEquiv k n).surjective] at hh
  exact hh.symm
theorem oddClassFusion (n : ℕ) (hn : 0 < n) :
    OddClassFusion (finiteGeometry k hu) n := by
  apply oddClassFusion_of_connected_centralizers_of_lang _ n
    (fixedCentralizer_connected k hu n hn)
  intro x _ hC
  exact centralizerRestriction_lang_surjective_of_frobenius_differential_eq_zero
    _ (frobenius_differential_zero k hu) n hn x hC

theorem elementaryClassBound (n : ℕ) (hn : 0 < n) :
    ElementaryClassBound (finiteGeometry k hu) n :=
  elementaryClassBound_of_generation_of_fusion_of_ambientCount _ n
    (elementary_eq_top k hu n hn) (oddClassFusion k hu n hn)
    (ambientClassBound k hu n hn)
end Triality.RestrictedWeights.Concrete.TorusGeometrySource
