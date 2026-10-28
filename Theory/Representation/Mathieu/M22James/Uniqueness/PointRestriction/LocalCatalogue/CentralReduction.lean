module

public import Theory.Representation.SL3FourNaturalDual.CentralSections
public import Theory.Representation.SubspaceQuotient

/-!
# The central field for small SL₃(4) modules

The relation z²+z+1=0 for the actual central scalar z equips any binary
module with canonical F₄ scalars. All group operators are linear over this
field. Submodules, quotient actions, and intertwining equivalences retain
the relation; the invariant-subspace lattice is unchanged. In particular,
binary dimension twelve becomes field dimension six, without an
irreducibility or semisimplicity hypothesis.

This is the SL₃(4) reduction needed in James (1973), Lemma 8.3, cited in
Aschbacher–Smith H.12.1(1), printed pp.393–394. It generalizes the construction
in PointRestriction/CentralField.lean without importing any Mathieu module.
It does not assert the constituent or extension classification.
-/

@[expose] public section

namespace Representation.SL3FourLocalCatalogue

abbrev F := SL2FourNatural.F
abbrev SL := SL3FourNaturalDual.SL
abbrev z := SL3FourNaturalDual.centralScalar

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

/-- The nontrivial central-character relation on the entire binary module. -/
def CentralQuadratic (σ : Representation (ZMod 2) SL U) : Prop :=
  σ z ^ 2 + σ z + 1 = 0

variable (σ : Representation (ZMod 2) SL U) (hq : CentralQuadratic σ)

include hq in
lemma centralQuadratic_apply (v : U) : σ z (σ z v) + σ z v + v = 0 :=
  LinearMap.congr_fun hq v

/-- Evaluation of the concrete quadratic field at the central operator. -/
noncomputable def scalarMap : F →ₐ[ZMod 2] Module.End (ZMod 2) U :=
  QuadraticAlgebra.lift ⟨σ z, by
    have he : σ z ^ 2 = -(σ z + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [CentralQuadratic, add_assoc] using hq
    have hn (f : Module.End (ZMod 2) U) : -f = f := by
      rw [← neg_one_smul (ZMod 2), show (-1 : ZMod 2) = 1 by decide, one_smul]
    simpa only [pow_two, hn, one_smul, add_comm] using he⟩

/-- Canonical central-field scalars on the original additive group. -/
@[instance_reducible] noncomputable def fieldModule : Module F U :=
  Module.compHom U (scalarMap σ hq).toRingHom

lemma fieldTower : letI := fieldModule σ hq
    IsScalarTower (ZMod 2) F U := by
  let := fieldModule σ hq
  constructor
  intro r a v
  change scalarMap σ hq (r • a) v = r • (scalarMap σ hq a v)
  rw [map_smul]
  rfl

lemma field_smul_formula (a : F) (v : U) : letI := fieldModule σ hq
    a • v = a.re • v + a.im • σ z v := rfl

/-- The original action is linear over its canonical central field. -/
noncomputable def fieldRepresentation : letI := fieldModule σ hq
    Representation F SL U := by
  letI := fieldModule σ hq
  refine { toFun := fun g => { (σ g).toAddHom with map_smul' := ?_ }
           map_one' := ?_, map_mul' := ?_ }
  · intro a v
    change σ g (a.re • v + a.im • σ z v) =
      a.re • σ g v + a.im • σ z (σ g v)
    rw [map_add, map_smul, map_smul]
    apply congrArg (fun w => a.re • σ g v + a.im • w)
    have hh := congrArg (fun x => σ x v) (SL3FourNaturalDual.centralScalar_commute g)
    simpa only [map_mul, Module.End.mul_apply] using hh.symm
  · ext v
    exact LinearMap.congr_fun σ.map_one v
  · intro g h
    ext v
    exact LinearMap.congr_fun (σ.map_mul g h) v

lemma fieldRepresentation_apply (g : SL) (v : U) :
    fieldRepresentation σ hq g v = σ g v := rfl

lemma field_scalar (v : U) : letI := fieldModule σ hq
    σ z v = (QuadraticAlgebra.omega : F) • v := by
  change σ z v = (0 : ZMod 2) • v + (1 : ZMod 2) • σ z v
  simp only [zero_smul, one_smul, zero_add]

lemma field_finrank : letI := fieldModule σ hq
    2 * Module.finrank F U = Module.finrank (ZMod 2) U := by
  let := fieldModule σ hq
  let := fieldTower σ hq
  have h := Module.finrank_mul_finrank (ZMod 2) F U
  rwa [QuadraticAlgebra.finrank_eq_two] at h

lemma field_finrank_six (hd : Module.finrank (ZMod 2) U = 12) :
    letI := fieldModule σ hq
    Module.finrank F U = 6 := by
  let := fieldModule σ hq
  have h := field_finrank σ hq
  rw [hd] at h
  omega

lemma fieldRepresentation_faithful (hf : Function.Injective σ) :
    letI := fieldModule σ hq
    Function.Injective (fieldRepresentation σ hq) := by
  let := fieldModule σ hq
  intro g h he
  apply hf
  ext v
  exact LinearMap.congr_fun he v

/-- Binary invariant subspaces are exactly the central-field invariant subspaces. -/
noncomputable def subrepresentationEquiv : letI := fieldModule σ hq
    Subrepresentation σ ≃o Subrepresentation (fieldRepresentation σ hq) := by
  letI := fieldModule σ hq
  letI := fieldTower σ hq
  refine {
    toFun := fun N => {
      toSubmodule := {
        carrier := N
        zero_mem' := N.toSubmodule.zero_mem
        add_mem' := N.toSubmodule.add_mem
        smul_mem' := ?_ }
      apply_mem_toSubmodule := fun g _ hv => N.apply_mem_toSubmodule g hv }
    invFun := fun N => {
      toSubmodule := N.toSubmodule.restrictScalars (ZMod 2)
      apply_mem_toSubmodule := fun g _ hv => N.apply_mem_toSubmodule g hv }
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := fun {_ _} => Iff.rfl }
  · intro a v hv
    exact N.toSubmodule.add_mem (N.toSubmodule.smul_mem _ hv)
      (N.toSubmodule.smul_mem _ (N.apply_mem_toSubmodule z hv))
  · intro N
    apply Subrepresentation.toSubmodule_injective
    rfl
  · intro N
    apply Subrepresentation.toSubmodule_injective
    rfl

lemma subrepresentation_finrank (N : Subrepresentation σ) :
    letI := fieldModule σ hq
    2 * Module.finrank F (subrepresentationEquiv σ hq N).toSubmodule =
      Module.finrank (ZMod 2) N.toSubmodule := by
  let := fieldModule σ hq
  let := fieldTower σ hq
  let e : N.toSubmodule ≃ₗ[ZMod 2] (subrepresentationEquiv σ hq N).toSubmodule := {
    toFun v := ⟨v.val, v.property⟩
    invFun v := ⟨v.val, v.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  rw [e.finrank_eq]
  have h := Module.finrank_mul_finrank (ZMod 2) F
    (subrepresentationEquiv σ hq N).toSubmodule
  rwa [QuadraticAlgebra.finrank_eq_two] at h

include hq in
lemma centralQuadratic_subrepresentation (N : Subrepresentation σ) :
    CentralQuadratic N.toRepresentation := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact centralQuadratic_apply σ hq v

include hq in
lemma centralQuadratic_quotient (N : Subrepresentation σ) :
    CentralQuadratic N.quotientRepresentation := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change N.toSubmodule.mkQ (σ z (σ z v)) +
      N.toSubmodule.mkQ (σ z v) + N.toSubmodule.mkQ v = 0
    rw [← map_add, ← map_add, centralQuadratic_apply σ hq, map_zero]

include hq in
lemma subrepresentation_even_finrank (N : Subrepresentation σ) :
    Even (Module.finrank (ZMod 2) N.toSubmodule) := by
  rw [← subrepresentation_finrank σ hq N]
  exact even_two_mul _

variable {T : Type*} [AddCommGroup T] [Module (ZMod 2) T]
  (τ : Representation (ZMod 2) SL T) (ht : CentralQuadratic τ)

/-- Every binary equivalence automatically respects the canonical field scalars. -/
noncomputable def equivOverField (e : σ.Equiv τ) :
    letI := fieldModule σ hq
    letI := fieldModule τ ht
    (fieldRepresentation σ hq).Equiv (fieldRepresentation τ ht) := by
  letI := fieldModule σ hq
  letI := fieldModule τ ht
  refine .mk { e.toLinearEquiv.toAddEquiv with map_smul' := ?_ } ?_
  · intro a v
    change e (a.re • v + a.im • σ z v) = a.re • e v + a.im • τ z (e v)
    rw [map_add, map_smul, map_smul]
    apply congrArg (fun w => a.re • e v + a.im • w)
    exact LinearMap.congr_fun (e.isIntertwining' z) v
  · intro g
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (e.isIntertwining' g) v

/-- Field-linear equivalences descend to the original binary representations. -/
noncomputable def equivOfField
    (e : letI := fieldModule σ hq
      letI := fieldModule τ ht
      (fieldRepresentation σ hq).Equiv (fieldRepresentation τ ht)) : σ.Equiv τ := by
  letI := fieldModule σ hq
  letI := fieldTower σ hq
  letI := fieldModule τ ht
  letI := fieldTower τ ht
  refine .mk (e.toLinearEquiv.restrictScalars (ZMod 2)) ?_
  intro g
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun (e.isIntertwining' g) v

include hq in
/-- The central relation is transported by an actual binary module equivalence. -/
lemma centralQuadratic_of_equiv (e : σ.Equiv τ) : CentralQuadratic τ := by
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
  have he (x : U) : e (σ z x) = τ z (e x) :=
    LinearMap.congr_fun (e.isIntertwining' z) x
  change τ z (τ z (e v)) + τ z (e v) + e v = 0
  have h := congrArg e (centralQuadratic_apply σ hq v)
  simpa only [map_add, map_zero, he] using h

/-- Irreducibility is unchanged by the central field, because the entire
invariant-subspace lattice is unchanged. -/
lemma field_isIrreducible_iff : letI := fieldModule σ hq
    IsIrreducible (fieldRepresentation σ hq) ↔ IsIrreducible σ := by
  let := fieldModule σ hq
  exact (subrepresentationEquiv σ hq).isSimpleOrder_iff.symm

end Representation.SL3FourLocalCatalogue
