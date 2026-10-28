module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.ReflectionLifts
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.Lang

/-!
# Vanishing roots in a toral centralizer's identity component

The literal root-weight equation makes a root subgroup centralize a torus
point exactly when the root evaluates to one. Its connected image therefore
lies in the identity component. Both opposite roots vanish simultaneously,
so the actual three-factor SL₂ Weyl word lies there as well.

Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*, §3.9(a).
These are the geometric generators used by the integral F4 stabilizer proof.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
open RootModel.Corrected
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
attribute [local instance] torusGroup ClosedSubgroup.carrierAlgebraicGroup

omit [CharP F 2] in
private theorem rawCharacter_root (r : typeF4Roots) :
    rawCharacter (F := F) (F4WeightAction.rootWeight r) = F4Chevalley.rootWeight r := by
  apply Additive.ofMul.injective
  exact (characterEquiv_apply _).symm.trans (characterEquiv_root r)

omit [CharP F 2] in
private theorem root_point_eq_one_of_evaluation_zero
    (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (r : typeF4Roots) (hr : rawEvaluation t (F4WeightAction.rootWeight r) = 0) :
    (F4Chevalley.rootWeight r).pointCharacter t = 1 := by
  rw [rawEvaluation_apply, rawCharacter_root] at hr
  have he := congrArg Additive.toMul hr
  exact congrArg Units.val he

private theorem root_le_centralizer_of_weight_one
    (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (r : typeF4Roots) (hr : (F4Chevalley.rootWeight r).pointCharacter t = 1) :
    F4Chevalley.rootSubgroup r ≤ pointCentralizer (F4Chevalley.splitTorus.includePoint t) := by
  let X := F4Chevalley.rootSubgroup (k := F) r
  let : AlgebraicGroup X.carrierVariety := X.carrierAlgebraicGroup
  let x : OneParameterParametrization X.carrierVariety :=
    Classical.choice (((rootData_isRealization_charTwo (F := F)).2.2.1 ⟨r⟩).1.2)
  have hEq : RootWeightEquation F4Chevalley.splitTorus X (F4Chevalley.rootWeight r) :=
    ((rootData_isRealization_charTwo (F := F)).2.2.1 ⟨r⟩).2
  intro y hy
  let yX : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨y, hy⟩
  let qy : Variety.Point (KPlus F) := x.inv.onPoints yX
  let a : F := Multiplicative.toAdd (additiveGroupPointEquiv F qy)
  have hqa : kPlusPoint a = qy := by
    apply (additiveGroupPointEquiv F).injective
    exact Multiplicative.ofAdd.apply_symm_apply (additiveGroupPointEquiv F qy)
  have hxa : X.includePoint (x.value a) = y := by
    change (X.pointEquiv (x.hom.onPoints (kPlusPoint a))).val = y
    rw [hqa, x.inv_hom_id]
    exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨y, hy⟩)
  have hconj := hEq x a t
  rw [hr, one_mul, hxa] at hconj
  change y ∈ Subgroup.centralizer ({F4Chevalley.splitTorus.includePoint t} : Set (PointGroup F))
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc
    y * F4Chevalley.splitTorus.includePoint t =
      F4Chevalley.splitTorus.includePoint t *
        ((F4Chevalley.splitTorus.includePoint t)⁻¹ * y * F4Chevalley.splitTorus.includePoint t) := by
      simp only [mul_assoc, mul_inv_cancel_left]
    _ = F4Chevalley.splitTorus.includePoint t * y := congrArg (fun z => _ * z) hconj

theorem root_le_centralizer_component_of_evaluation_zero
    (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (r : typeF4Roots) (hr : rawEvaluation t (F4WeightAction.rootWeight r) = 0) :
    F4Chevalley.rootSubgroup r ≤
      (pointCentralizer (F4Chevalley.splitTorus.includePoint t)).identityComponentAmbient := by
  apply connected_closedSubgroup_le_identityComponentAmbient
    _ _ (F4Chevalley.rootSubgroup_isConnected r)
  exact root_le_centralizer_of_weight_one t r (root_point_eq_one_of_evaluation_zero t r hr)

private theorem weyl_mem_of_root_subgroups
    {G : Variety F} [AlgebraicGroup G] (T X Y : ClosedSubgroup G)
    (d : BinaryOppositeRootSL2Chart T X Y) (H : Subgroup (Variety.Point G))
    (hX : X.toSubgroup ≤ H) (hY : Y.toSubgroup ≤ H) : d.weyl ∈ H := by
  rw [BinaryOppositeRootSL2Chart.weyl_eq]
  exact H.mul_mem (H.mul_mem (hX (X.pointEquiv (d.plus.value 1)).property)
    (hY (Y.pointEquiv (d.minus.value 1)).property))
    (hX (X.pointEquiv (d.plus.value 1)).property)

theorem reflectionLift_mem_component_of_evaluation_zero
    (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (r : typeF4Roots) (hr : rawEvaluation t (F4WeightAction.rootWeight r) = 0) :
    (reflectionLift (F := F) r).val ∈
      (pointCentralizer (F4Chevalley.splitTorus.includePoint t)).identityComponentAmbient := by
  have hplus := root_le_centralizer_component_of_evaluation_zero t r hr
  have hneg : (F4Chevalley.rootWeight (typeF4RootPairing.reflectionPerm r r)).pointCharacter t = 1 := by
    have he := (rootData_isRealization_charTwo (F := F)).2.2.2.1 ⟨r⟩
    change F4Chevalley.rootWeight (k := F) (typeF4RootPairing.reflectionPerm r r) =
      (F4Chevalley.rootWeight r)⁻¹ at he
    rw [he]
    have hi := (torusPointEval _ t).map_inv (F4Chevalley.rootWeight r)
    change ((torusPointEval _ t) ((F4Chevalley.rootWeight r)⁻¹)).val = 1
    rw [hi]
    have hz := root_point_eq_one_of_evaluation_zero t r hr
    change ((torusPointEval _ t) (F4Chevalley.rootWeight r)).val = 1 at hz
    rw [Units.val_inv_eq_inv_val, hz, inv_one]
  have hminus := connected_closedSubgroup_le_identityComponentAmbient
    _ _ (F4Chevalley.rootSubgroup_isConnected (typeF4RootPairing.reflectionPerm r r))
    (root_le_centralizer_of_weight_one t _ hneg)
  rw [reflectionLift_val]
  exact weyl_mem_of_root_subgroups _ _ _ (reflectionChart r) _ hplus hminus
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
