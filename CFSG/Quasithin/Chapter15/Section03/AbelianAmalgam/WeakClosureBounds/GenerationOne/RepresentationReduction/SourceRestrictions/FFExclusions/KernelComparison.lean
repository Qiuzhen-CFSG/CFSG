module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FaithfulSections
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.OffenderReduction

/-!
# Identifying the actual faithful section image

Equality of the actual action kernel with the kernel of a specified model
map gives a coherent isomorphism from the action image to the model. The
isomorphism carries every subgroup image, including the Borel, through that
same map. The transported representation is faithful and has the original
action on all lifts.

For a nontrivial component orbit, the section kernel is already known to
centralize that orbit. A reverse containment and a model centralizer bound
therefore identify the kernel exactly. Neither a central cover nor a section
kernel is silently discarded. For every nontrivial quasisimple action, the
central simple quotient is also identified with that of its actual image.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), F.9.18(6),
printed pp.325--326, as used in 15.3.65 on p.1152.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions
variable {D E V : Type*} [Group D] [Group E] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
/-- The faithful image is the specified quotient model when their literal kernels agree. -/
noncomputable def actionImageModelEquiv (q : D →* E) (hq : Function.Surjective q)
    (hker : (actionHom ρ).ker = q.ker) : actionImage ρ ≃* E :=
  (QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq))
/-- The comparison sends the action of g to the specified model image of g. -/
@[simp] theorem actionImageModelEquiv_actionHom (q : D →* E) (hq : Function.Surjective q)
    (hker : (actionHom ρ).ker = q.ker) (g : D) :
    actionImageModelEquiv ρ q hq hker (actionHom ρ g) = q g := by
  have he : QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective (QuotientGroup.mk g) = actionHom ρ g := rfl
  rw [← he]
  simp only [actionImageModelEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- Every subgroup, in particular the Borel, uses the same model comparison. -/
theorem actionImageModelEquiv_subgroup (q : D →* E) (hq : Function.Surjective q)
    (hker : (actionHom ρ).ker = q.ker) (A : Subgroup D) :
    (actionSubgroup ρ A).map (actionImageModelEquiv ρ q hq hker).toMonoidHom = A.map q := by
  rw [actionSubgroup, Subgroup.map_map]
  congr 1
  ext g
  exact actionImageModelEquiv_actionHom ρ q hq hker g

/-- Transport the tautological faithful image action to the actual quotient model. -/
noncomputable def modelRepresentation (q : D →* E) (hq : Function.Surjective q)
    (hker : (actionHom ρ).ker = q.ker) : Representation (ZMod 2) E V :=
  (imageRepresentation ρ).comp (actionImageModelEquiv ρ q hq hker).symm.toMonoidHom

/-- The model action is faithful; no faithfulness of the original ambient group is required. -/
theorem modelRepresentation_faithful (q : D →* E) (hq : Function.Surjective q)
    (hker : (actionHom ρ).ker = q.ker) :
    Function.Injective (modelRepresentation ρ q hq hker) :=
  (imageRepresentation_injective ρ).comp (actionImageModelEquiv ρ q hq hker).symm.injective

/-- Lifting a model element recovers the original linear action. -/
@[simp] theorem modelRepresentation_apply (q : D →* E) (hq : Function.Surjective q)
    (hker : (actionHom ρ).ker = q.ker) (g : D) (v : V) :
    modelRepresentation ρ q hq hker (q g) v = ρ g v := by
  rw [← actionImageModelEquiv_actionHom ρ q hq hker g]
  change imageRepresentation ρ
    ((actionImageModelEquiv ρ q hq hker).symm
      ((actionImageModelEquiv ρ q hq hker) (actionHom ρ g))) v = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- FF status is preserved by the coherent isomorphism with the actual image. -/
theorem isFFModule_model_iff (q : D →* E) (hq : Function.Surjective q)
    (hker : (actionHom ρ).ker = q.ker) :
    IsFFModule (modelRepresentation ρ q hq hker) ↔ IsFFModule (imageRepresentation ρ) := by
  let e := actionImageModelEquiv ρ q hq hker
  constructor
  · intro h
    exact h.map_equivariant _ _ e.symm.toMonoidHom e.symm.injective
      (LinearEquiv.refl _ _) (fun _ _ => rfl)
  · intro h
    apply h.map_equivariant _ _ e.toMonoidHom e.injective (LinearEquiv.refl _ _)
    intro g v
    change imageRepresentation ρ g v = imageRepresentation ρ (e.symm (e g)) v
    rw [e.symm_apply_apply]

/-- The same comparison preserves the strict offender inequality. -/
theorem isStrongFFModule_model_iff (q : D →* E) (hq : Function.Surjective q)
    (hker : (actionHom ρ).ker = q.ker) :
    IsStrongFFModule (modelRepresentation ρ q hq hker) ↔
      IsStrongFFModule (imageRepresentation ρ) := by
  let e := actionImageModelEquiv ρ q hq hker
  constructor
  · intro h
    exact strongFF_map_equivariant _ _ e.symm.toMonoidHom e.symm.injective
      (LinearEquiv.refl _ _) (fun _ _ => rfl) h
  · intro h
    apply strongFF_map_equivariant _ _ e.toMonoidHom e.injective (LinearEquiv.refl _ _) _ h
    intro g v
    change imageRepresentation ρ g v = imageRepresentation ρ (e.symm (e g)) v
    rw [e.symm_apply_apply]

/-- The component-orbit centralizer bound determines the actual action kernel. -/
theorem action_kernel_eq_of_component_orbit
    (q : D →* E) (K T : Subgroup D) (hK : Theory.GroupTheory.IsComponent D K)
    (htrivial : q.ker ≤ (actionHom ρ).ker)
    (hcentralizer : centralizer (conjugateSpanBy K T : Set D) ≤ q.ker)
    (hn : ¬ ∀ l ∈ conjugateSpanBy K T, ∀ v, ρ l v = v) :
    (actionHom ρ).ker = q.ker :=
  le_antisymm ((action_kernel_le_centralizer_of_component_orbit ρ K T hK hn).trans
    hcentralizer) htrivial

/-- Nontrivial action gives a nontrivial actual action image. -/
theorem nontrivial_actionImage (hn : ¬ ∀ g v, ρ g v = v) : Nontrivial (actionImage ρ) := by
  push Not at hn
  obtain ⟨g, v, h⟩ := hn
  exact ⟨⟨actionHom ρ g, 1, fun he => h ((actionHom_eq_one_iff ρ g).mp he v)⟩⟩

/-- A nontrivial action image of a quasisimple group is quasisimple. -/
theorem quasisimple_actionImage [Theory.GroupTheory.IsQuasisimple D]
    (hn : ¬ ∀ g v, ρ g v = v) : Theory.GroupTheory.IsQuasisimple (actionImage ρ) := by
  let : Nontrivial (actionImage ρ) := nontrivial_actionImage ρ hn
  exact Theory.GroupTheory.IsQuasisimple.of_surjective (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective

/-- The preimage of the image center is exactly the original center, even when the action has central kernel. -/
theorem actionImage_center_comap [Theory.GroupTheory.IsQuasisimple D]
    (hn : ¬ ∀ g v, ρ g v = v) :
    (center (actionImage ρ)).comap (actionHom ρ) = center D := by
  let : Theory.GroupTheory.IsQuasisimple (actionImage ρ) := quasisimple_actionImage ρ hn
  let : Nontrivial (actionImage ρ) := nontrivial_actionImage ρ hn
  have hsurj : Function.Surjective (actionHom ρ) := ρ.asGroupHom.rangeRestrict_surjective
  apply le_antisymm
  · rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top
        ((center (actionImage ρ)).comap (actionHom ρ)) with hc | ht
    · exact hc
    · have hc : center (actionImage ρ) = ⊤ := by
        apply Subgroup.comap_injective hsurj
        simpa using ht
      exact (Group.IsPerfect.not_isMulCommutative (actionImage ρ) (center_eq_top_iff.mp hc)).elim
  · intro g hg
    rw [Subgroup.mem_comap, mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := hsurj y
    simpa only [map_mul] using congrArg (actionHom ρ) (mem_center_iff.mp hg y)

/-- The actual section image has the same central simple quotient. Apply this to the action restricted to each component. -/
noncomputable def actionImageCentralQuotientEquiv [Theory.GroupTheory.IsQuasisimple D]
    (hn : ¬ ∀ g v, ρ g v = v) :
    D ⧸ center D ≃* actionImage ρ ⧸ center (actionImage ρ) := by
  let q := (QuotientGroup.mk' (center (actionImage ρ))).comp (actionHom ρ)
  have hker : q.ker = center D := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact actionImage_center_comap ρ hn
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp ρ.asGroupHom.rangeRestrict_surjective))
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions
