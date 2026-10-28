module

public import Theory.Representation.FirstCohomologyLinearTransport
public import CFSG.Quasithin.ChapterH.Section10To12.TripleJames
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.CentralField

/-!
# The central four-element field on triple Mathieu modules

Pulling back to the genuine matrix cover lets us reuse its central-field
construction on the original binary carrier. Its scalars are explicitly
`a.re • v + a.im • ρ(z) v`, where z is the transported generator of the
actual center. The unchanged group action is linear for these scalars,
and restriction of scalars is identified by the identity intertwiner.

At binary dimension twelve the field dimension is six. Binary module
equivalences respect this field structure, retaining James uniqueness with
actual intertwining linear equivalences. This proves the scalar-extension
step of H.12.1(2); it does not yet construct its invariant Hermitian form.

Source: Aschbacher–Smith H.12.1(1–2), printed pp.393–394 (PDF pp.404–405).
-/

@[expose] public section

open Representation Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterH.Section10To12.IsTripleM22
namespace FieldModel
abbrev F := M22TripleCover.Uniqueness.PointRestriction.F
variable {L W : Type*} [Group L] [Finite L] [AddCommGroup W] [Module (ZMod 2) W]
  (hL : IsTripleM22 L) (ρ : Representation (ZMod 2) L W)
  (hf : Function.Injective ρ) [ρ.IsIrreducible]

/-- Pull the original action back to the genuine concrete cover. -/
noncomputable def onModel : Representation (ZMod 2) M22TripleCover W :=
  ρ.comp hL.groupEquiv.symm.toMonoidHom

instance onModel_irreducible : (onModel hL ρ).IsIrreducible :=
  (Representation.irreducible_comp_surjective_iff hL.groupEquiv.symm.toMonoidHom
    hL.groupEquiv.symm.surjective ρ).mpr inferInstance

omit [ρ.IsIrreducible] in
include hf in
theorem onModel_faithful : Function.Injective (onModel hL ρ) :=
  hf.comp hL.groupEquiv.symm.injective

/-- The compatible F₄-module structure on the original binary carrier. -/
@[instance_reducible] noncomputable def moduleStructure : Module F W :=
  M22TripleCover.Uniqueness.PointRestriction.fieldModule (onModel hL ρ)
    (onModel_faithful hL ρ hf)

theorem tower : letI := moduleStructure hL ρ hf
    IsScalarTower (ZMod 2) F W :=
  M22TripleCover.Uniqueness.PointRestriction.fieldTower (onModel hL ρ)
    (onModel_faithful hL ρ hf)

/-- The same group action, now linear over the central field. -/
noncomputable def representation : letI := moduleStructure hL ρ hf
    Representation F L W :=
  (M22TripleCover.Uniqueness.PointRestriction.fieldRepresentation (onModel hL ρ)
    (onModel_faithful hL ρ hf)).comp hL.groupEquiv.toMonoidHom

theorem representation_apply (g : L) (v : W) :
    representation hL ρ hf g v = ρ g v := by
  change ρ (hL.groupEquiv.symm (hL.groupEquiv g)) v = ρ g v
  rw [hL.groupEquiv.symm_apply_apply]

theorem finrank (hd : Module.finrank (ZMod 2) W = 12) :
    letI := moduleStructure hL ρ hf
    Module.finrank F W = 6 :=
  M22TripleCover.Uniqueness.PointRestriction.field_finrank (onModel hL ρ)
    (onModel_faithful hL ρ hf) hd

theorem scalar (v : W) : letI := moduleStructure hL ρ hf
    ρ hL.centralScalar v = (QuadraticAlgebra.omega : F) • v :=
  M22TripleCover.Uniqueness.PointRestriction.field_scalar (onModel hL ρ)
    (onModel_faithful hL ρ hf) v

theorem faithful : letI := moduleStructure hL ρ hf
    Function.Injective (representation hL ρ hf) := by
  let := moduleStructure hL ρ hf
  intro g h he
  apply hf
  ext v
  simpa only [representation_apply] using LinearMap.congr_fun he v

/-- The identity map identifies scalar restriction with the original binary action. -/
noncomputable def restrictionEquiv : letI := moduleStructure hL ρ hf
    letI := tower hL ρ hf
    Representation.Equiv (Representation.restrictScalars (k := ZMod 2) (representation hL ρ hf)) ρ := by
  let := moduleStructure hL ρ hf
  let := tower hL ρ hf
  refine .mk (LinearEquiv.refl (ZMod 2) W) ?_
  intro g
  ext v
  exact representation_apply hL ρ hf g v

/-- Explicit compatibility of the constructed scalars with the central operator. -/
theorem smul_formula (a : F) (v : W) : letI := moduleStructure hL ρ hf
    a • v = a.re • v + a.im • ρ hL.centralScalar v := rfl

/-- A binary intertwiner is linear for the field structures forced by the same center. -/
noncomputable def equivOverField
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) L V) (hσ : Function.Injective σ) [σ.IsIrreducible]
    (e : Representation.Equiv ρ σ) :
    letI := moduleStructure hL ρ hf
    letI := moduleStructure hL σ hσ
    Representation.Equiv (representation hL ρ hf) (representation hL σ hσ) := by
  letI := moduleStructure hL ρ hf
  letI := moduleStructure hL σ hσ
  refine .mk { e.toLinearEquiv.toAddEquiv with map_smul' := ?_ } ?_
  · intro a v
    change e (a.re • v + a.im • ρ hL.centralScalar v) =
      a.re • e v + a.im • σ hL.centralScalar (e v)
    rw [map_add, map_smul, map_smul]
    apply congrArg (fun w => a.re • e v + a.im • w)
    exact LinearMap.congr_fun (e.isIntertwining' hL.centralScalar) v
  · intro g
    ext v
    change e (representation hL ρ hf g v) = representation hL σ hσ g (e v)
    rw [representation_apply, representation_apply]
    exact LinearMap.congr_fun (e.isIntertwining' g) v

/-- James uniqueness retains the field action and the actual intertwining map. -/
theorem equiv_canonical_of_finrank_twelve (hd : Module.finrank (ZMod 2) W = 12) :
    letI := moduleStructure hL ρ hf
    letI := moduleStructure hL hL.binaryRepresentation hL.binaryRepresentation_faithful
    Nonempty (Representation.Equiv (representation hL ρ hf)
      (representation hL hL.binaryRepresentation hL.binaryRepresentation_faithful)) := by
  obtain ⟨e⟩ := hL.equiv_binaryRepresentation_of_finrank_twelve ρ hf hd
  exact ⟨equivOverField hL ρ hf hL.binaryRepresentation hL.binaryRepresentation_faithful e⟩

end FieldModel
end CFSG.Quasithin.ChapterH.Section10To12.IsTripleM22
