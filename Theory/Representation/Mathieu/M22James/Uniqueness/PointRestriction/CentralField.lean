module

public import Theory.Representation.Mathieu.M22James.Uniqueness.Reduction
public import Theory.Representation.SL2FourNaturalOrbits.Model

/-!
# Central field structure on Mathieu point-stabilizer restrictions

The distinguished central element of the genuine triple cover satisfies
X² + X + 1 in every faithful irreducible binary representation. Evaluating
the concrete quadratic field at that operator supplies compatible F₄
scalars on the original carrier. The group action is F₄-linear, and binary
dimension twelve becomes F₄ dimension six.

Because the actual point stabilizer contains the central element, its
binary invariant subspaces are exactly its F₄ invariant subspaces. We
retain this as an order isomorphism, together with the dimension formula.
Every binary equivalence of the restricted modules is automatically linear
over these specified F₄ structures, and conversely a field equivalence
descends to the original binary actions.

These are reductions for James (1973), Lemma 8.3, used in Aschbacher–Smith
H.12.1(1), printed pp.393–394. They do not classify the restriction, assume
it irreducible or semisimple, or identify the subgroup with SL₃(4).
The four-element field is reused from `SL2FourNaturalOrbits.Model`.
-/

@[expose] public section

open Representation
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction
/-- The concrete four-element field with distinguished root of X² + X + 1. -/
abbrev F := Representation.SL2FourNatural.F
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) M22TripleCover W) [ρ.IsIrreducible]
  (hf : Function.Injective ρ)

/-- Evaluate the quadratic field at the actual central operator. -/
noncomputable def scalarMap : F →ₐ[ZMod 2] Module.End (ZMod 2) W :=
  QuadraticAlgebra.lift ⟨ρ scalar, by
    have h := scalar_quadratic ρ hf
    have he : ρ scalar ^ 2 = -(ρ scalar + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_assoc] using h
    have hn (f : Module.End (ZMod 2) W) : -f = f := by
      rw [← neg_one_smul (ZMod 2), show (-1 : ZMod 2) = 1 by decide, one_smul]
    simpa only [pow_two, hn, one_smul, add_comm] using he⟩

/-- Scalar multiplication on the original carrier, without a choice of basis. -/
@[instance_reducible] noncomputable def fieldModule : Module F W :=
  Module.compHom W (scalarMap ρ hf).toRingHom

/-- The constructed action extends the existing binary scalars. -/
theorem fieldTower : letI := fieldModule ρ hf
    IsScalarTower (ZMod 2) F W := by
  let := fieldModule ρ hf
  constructor
  intro r a v
  change scalarMap ρ hf (r • a) v = r • (scalarMap ρ hf a v)
  rw [map_smul]
  rfl

/-- Scalar multiplication expressed using the identity and the central action. -/
lemma field_smul_formula (r : F) (v : W) :
    letI := fieldModule ρ hf
    r • v = r.re • v + r.im • ρ scalar v := rfl

/-- The same full group action over the field forced by its central element. -/
noncomputable def fieldRepresentation : letI := fieldModule ρ hf
    Representation F M22TripleCover W := by
  letI := fieldModule ρ hf
  refine { toFun := fun g => { (ρ g).toAddHom with map_smul' := ?_ }
           map_one' := ?_, map_mul' := ?_ }
  · intro a v
    change ρ g (a.re • v + a.im • ρ scalar v) =
      a.re • ρ g v + a.im • ρ scalar (ρ g v)
    rw [map_add, map_smul, map_smul]
    apply congrArg (fun w => a.re • ρ g v + a.im • w)
    have he : g * scalar = scalar * g := (Subgroup.mem_center_iff.mp scalar_mem_center g)
    have hh := congrArg (fun x => ρ x v) he
    simpa only [map_mul, Module.End.mul_apply] using hh
  · ext v
    exact LinearMap.congr_fun ρ.map_one v
  · intro g h
    ext v
    exact LinearMap.congr_fun (ρ.map_mul g h) v

/-- A twelve-dimensional binary module has dimension six over the central field. -/
lemma field_finrank (hd : Module.finrank (ZMod 2) W = 12) :
    letI := fieldModule ρ hf
    Module.finrank F W = 6 := by
  let := fieldModule ρ hf
  let := fieldTower ρ hf
  have h := Module.finrank_mul_finrank (ZMod 2) F W
  rw [QuadraticAlgebra.finrank_eq_two, hd] at h
  omega


/-- The scalar as an element of the actual subgroup. -/
def pointScalar : pointStabilizer := ⟨scalar, scalar_mem_pointStabilizer⟩

/-- No underlying group operator changes when extending the scalars. -/
lemma fieldRepresentation_apply (g : M22TripleCover) (v : W) :
    fieldRepresentation ρ hf g v = ρ g v := rfl

/-- The chosen primitive scalar acts as the distinguished central element itself. -/
lemma field_scalar (v : W) :
    letI := fieldModule ρ hf
    ρ scalar v = (QuadraticAlgebra.omega : F) • v := by
  change ρ scalar v = (0 : ZMod 2) • v + (1 : ZMod 2) • ρ scalar v
  simp only [zero_smul, one_smul, zero_add]

/-- Faithfulness is retained by the field-linear action. -/
lemma fieldRepresentation_faithful : letI := fieldModule ρ hf
    Function.Injective (fieldRepresentation ρ hf) := by
  let := fieldModule ρ hf
  intro g h he
  apply hf
  ext v
  exact LinearMap.congr_fun he v

/-- Literal restriction of the field-linear action to the actual point stabilizer. -/
noncomputable def pointFieldRepresentation : letI := fieldModule ρ hf
    Representation F pointStabilizer W :=
  (fieldRepresentation ρ hf).comp pointStabilizer.subtype

/-- The restricted field action is still the original group operator. -/
lemma pointFieldRepresentation_apply (g : pointStabilizer) (v : W) :
    pointFieldRepresentation ρ hf g v = ρ g v := rfl

/-- The field-linear restriction to the point stabilizer remains faithful. -/
lemma pointFieldRepresentation_faithful : letI := fieldModule ρ hf
    Function.Injective (pointFieldRepresentation ρ hf) := by
  let := fieldModule ρ hf
  intro g h he
  apply Subtype.ext
  apply hf
  ext v
  exact LinearMap.congr_fun he v

/-- The entire invariant-subspace lattice is unchanged by the central field structure. -/
noncomputable def pointSubrepresentationEquiv :
    letI := fieldModule ρ hf
    Subrepresentation (ρ.comp pointStabilizer.subtype) ≃o
      Subrepresentation (pointFieldRepresentation ρ hf) := by
  letI := fieldModule ρ hf
  letI := fieldTower ρ hf
  refine {
    toFun := fun U => {
      toSubmodule := {
        carrier := U
        zero_mem' := U.toSubmodule.zero_mem
        add_mem' := U.toSubmodule.add_mem
        smul_mem' := ?_ }
      apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule g hv }
    invFun := fun U => {
      toSubmodule := U.toSubmodule.restrictScalars (ZMod 2)
      apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule g hv }
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := fun {_ _} => Iff.rfl }
  · intro r v hv
    change r.re • v + r.im • ρ scalar v ∈ U.toSubmodule
    exact U.toSubmodule.add_mem (U.toSubmodule.smul_mem _ hv)
      (U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule pointScalar hv))
  · intro U
    apply Subrepresentation.toSubmodule_injective
    rfl
  · intro U
    apply Subrepresentation.toSubmodule_injective
    rfl

/-- Every invariant subspace has twice its field dimension as binary dimension. -/
lemma pointSubrepresentation_finrank (U : Subrepresentation (ρ.comp pointStabilizer.subtype)) :
    letI := fieldModule ρ hf
    2 * Module.finrank F (pointSubrepresentationEquiv ρ hf U).toSubmodule =
      Module.finrank (ZMod 2) U.toSubmodule := by
  let := fieldModule ρ hf
  let := fieldTower ρ hf
  let e : U.toSubmodule ≃ₗ[ZMod 2] (pointSubrepresentationEquiv ρ hf U).toSubmodule := {
    toFun v := ⟨v.val, v.property⟩
    invFun v := ⟨v.val, v.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  rw [e.finrank_eq]
  have h := Module.finrank_mul_finrank (ZMod 2) F
    (pointSubrepresentationEquiv ρ hf U).toSubmodule
  rwa [QuadraticAlgebra.finrank_eq_two] at h

include hf in
/-- In particular, every binary point-stabilizer submodule has even dimension. -/
lemma pointSubrepresentation_even_finrank (U : Subrepresentation (ρ.comp pointStabilizer.subtype)) :
    Even (Module.finrank (ZMod 2) U.toSubmodule) := by
  let := fieldModule ρ hf
  rw [← pointSubrepresentation_finrank ρ hf U]
  exact even_two_mul _

/-- A binary point-stabilizer equivalence respects the actual central field action. -/
noncomputable def pointEquivOverField
    (e : Representation.Equiv (ρ.comp pointStabilizer.subtype) pointRepresentation) :
    letI := fieldModule ρ hf
    letI := fieldModule binaryRepresentation binaryRepresentation_faithful
    Representation.Equiv (pointFieldRepresentation ρ hf)
      (pointFieldRepresentation binaryRepresentation binaryRepresentation_faithful) := by
  letI := fieldModule ρ hf
  letI := fieldModule binaryRepresentation binaryRepresentation_faithful
  refine .mk { e.toLinearEquiv.toAddEquiv with map_smul' := ?_ } ?_
  · intro a v
    change e (a.re • v + a.im • ρ scalar v) =
      a.re • e v + a.im • binaryRepresentation scalar (e v)
    rw [map_add, map_smul, map_smul]
    apply congrArg (fun w => a.re • e v + a.im • w)
    exact LinearMap.congr_fun (e.isIntertwining' pointScalar) v
  · intro g
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (e.isIntertwining' g) v

/-- A field-linear point-stabilizer equivalence descends to the original binary modules. -/
noncomputable def pointEquivOfField
    (e : letI := fieldModule ρ hf
      letI := fieldModule binaryRepresentation binaryRepresentation_faithful
      Representation.Equiv (pointFieldRepresentation ρ hf)
        (pointFieldRepresentation binaryRepresentation binaryRepresentation_faithful)) :
    Representation.Equiv (ρ.comp pointStabilizer.subtype) pointRepresentation := by
  letI := fieldModule ρ hf
  letI := fieldTower ρ hf
  letI := fieldModule binaryRepresentation binaryRepresentation_faithful
  letI := fieldTower binaryRepresentation binaryRepresentation_faithful
  refine .mk (e.toLinearEquiv.restrictScalars (ZMod 2)) ?_
  intro g
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun (e.isIntertwining' g) v

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction
