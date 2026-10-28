module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.NormalizerKernel
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.RootComponents
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Stabilizer.Basic

/-!
# Lifting the reflection kernel into a toral centralizer component

The image of the normalizer points in the centralizer identity component
contains each vanishing-root reflection. Every element of the reflection
kernel therefore has a component lift. Any other lift differs by a torus
point, and the torus is already in the identity component. The accompanying
evaluation identity identifies the exact stabilizer of an actual toral point.

Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*, §3.9(a).
The next source module consumes the proved characteristic-two F4 stabilizer
certificate, rather than assuming connectedness or a class-count input.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
open RootModel.Corrected
open BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
open BorelIntersectionGeometry
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
attribute [local instance] torusGroup

theorem torus_le_pointCentralizer
    (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety) :
    F4Chevalley.splitTorus ≤ pointCentralizer (F4Chevalley.splitTorus.includePoint t) := by
  intro s hs
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact (Subgroup.mem_centralizer_iff.mp
    (maximalTorus_le_centralizer splitTorus_isMaximal hs)
    _ (F4Chevalley.splitTorus.pointEquiv t).property).symm

theorem normalizer_centralizer_evaluation_fixed
    (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup)
    (hn : n.val ∈ pointCentralizer (F4Chevalley.splitTorus.includePoint t)) :
    ∀ a, rawEvaluation t (F4WeightAction.representation (normalizerWeyl n) a) = rawEvaluation t a := by
  have hp : (torusConjugation n⁻¹).onPoints t = t := by
    apply F4Chevalley.splitTorus.inclusion_injective
    change F4Chevalley.splitTorus.includePoint _ = F4Chevalley.splitTorus.includePoint t
    rw [torusConjugation_include, Subgroup.coe_inv, inv_inv]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hn
    change n.val * F4Chevalley.splitTorus.includePoint t =
      F4Chevalley.splitTorus.includePoint t * n.val at hc
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  intro a
  rw [rawEvaluation_normalizer, hp]

theorem normalizer_mem_component_of_reflectionKernel
    (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup)
    (hn : normalizerWeyl n ∈ F4WeightAction.Stabilizer.reflectionKernel (rawEvaluation t)) :
    n.val ∈ (pointCentralizer (F4Chevalley.splitTorus.includePoint t)).identityComponentAmbient := by
  let C := (pointCentralizer (F4Chevalley.splitTorus.includePoint t)).identityComponentAmbient.toSubgroup
  let N := (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup
  let H : Subgroup F4WeightAction.Weyl := (C.comap N.subtype).map normalizerWeyl
  have hle : F4WeightAction.Stabilizer.reflectionKernel (rawEvaluation t) ≤ H := by
    apply (Subgroup.closure_le _).2
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨reflectionLift r, reflectionLift_mem_component_of_evaluation_zero t r hr, ?_⟩
    exact normalizerWeyl_reflectionLift r
  obtain ⟨v, hv, he⟩ := hle hn
  have hk : normalizerWeyl (v⁻¹ * n) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have ht := mem_torus_of_normalizerWeyl_eq_one (v⁻¹ * n) hk
  have hTC := maximalTorus_le_identityComponentAmbient_of_le
    F4Chevalley.splitTorus (pointCentralizer (F4Chevalley.splitTorus.includePoint t))
    splitTorus_isMaximal (torus_le_pointCentralizer t)
  have hc := C.mul_mem hv (hTC ht)
  change v.val * (v.val⁻¹ * n.val) ∈ C at hc
  change n.val ∈ C
  simpa only [mul_inv_cancel_left] using hc

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
