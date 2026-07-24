/-
Authors: OpenAI
-/

module

public import Submission.FeitThompson.Representation.RepEnd
public import Submission.FeitThompson.Representation.ConjugateRep
public import Mathlib.FieldTheory.Fixed

/-!
# Inertia groups and endomorphism-algebra transport
-/

noncomputable section

namespace BenderSuzuki
namespace PFAppendixIV

universe u v w
/-- The identity element gives the canonical equivalence with the corresponding conjugate representation. -/
public noncomputable def conjugateRep_equiv_one
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) :
    rho ≃ₗ Representation.conjugateRep rho (1 : G) := by
  refine Representation.RepEquiv.mk (LinearEquiv.refl F V) ?_
  intro h
  ext x
  simp [Representation.conjugateRep_apply]

/-- Transport a conjugacy equivalence after conjugating both representations on the right. -/
public noncomputable def conjugateRep_equiv_mul_left
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) {a g : G}
    (e : rho ≃ₗ Representation.conjugateRep rho a) :
    Representation.conjugateRep rho g ≃ₗ
      Representation.conjugateRep rho (a * g) := by
  refine Representation.RepEquiv.mk e.toLinearEquiv ?_
  intro h
  ext x
  change e (rho ⟨g * h * g⁻¹,
    Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⟩ x) =
      rho ⟨(a * g) * h * (a * g)⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop (a * g)⟩ (e x)
  simpa only [Representation.conjugateRep_apply, mul_inv_rev, mul_assoc] using
    Representation.RepEquiv.isIntertwining e
      ⟨g * h * g⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⟩ x

/-- Move an equivalence between two conjugates back to the original representation. -/
public noncomputable def conjugateRep_diff_equiv
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) {g x : G}
    (e : Representation.conjugateRep rho g ≃ₗ
      Representation.conjugateRep rho x) :
    rho ≃ₗ Representation.conjugateRep rho (x * g⁻¹) := by
  refine Representation.RepEquiv.mk e.toLinearEquiv ?_
  intro h
  ext y
  let h' : H := ⟨g⁻¹ * h * g, by
    simpa using (inferInstance : H.Normal).conj_mem (h : G) h.2 g⁻¹⟩
  change e (rho h y) = (rho.conjugateRep (x * g⁻¹)) h (e y)
  simpa only [h', Representation.conjugateRep_apply, LinearMap.comp_apply,
    mul_inv_rev, inv_inv, mul_inv_cancel, mul_inv_cancel_left, mul_inv_cancel_right,
    mul_one, mul_assoc] using
    (Representation.RepEquiv.isIntertwining e h' y)

/-- The subgroup stabilizing the isomorphism class of a representation of a normal subgroup. -/
public noncomputable def representationInertiaSubgroup
    {F : Type v} [Field F] {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) : Subgroup G where
  carrier := {g | Nonempty (rho ≃ₗ Representation.conjugateRep rho g)}
  one_mem' := ⟨conjugateRep_equiv_one rho⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ea⟩ := ha
    obtain ⟨eb⟩ := hb
    exact ⟨eb.trans
      (conjugateRep_equiv_mul_left rho (g := b) ea)⟩
  inv_mem' := by
    intro a ha
    obtain ⟨ea⟩ := ha
    let eone := conjugateRep_equiv_one rho
    exact ⟨by
      simpa using
        (conjugateRep_diff_equiv rho (g := a) (x := 1)
          (ea.symm.trans eone))⟩

@[simp] public theorem mem_representationInertiaSubgroup_iff
    {F : Type v} [Field F] {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) (g : G) :
    g ∈ representationInertiaSubgroup H rho ↔
      Nonempty (rho ≃ₗ Representation.conjugateRep rho g) := Iff.rfl


/-- Intertwining endomorphisms are the same algebra as endomorphisms of the
corresponding group-algebra module. -/
public noncomputable def repEndAlgEquivModuleEnd
    {F : Type v} [Field F] {G : Type u} [Monoid G]
    {V : Type w} [AddCommGroup V] [Module F V]
    (rho : Representation F G V) :
    Representation.End rho ≃ₐ[F]
      Module.End (MonoidAlgebra F G) rho.asModule where
  toFun f := Representation.RepMap.equivLinearMapAsModule rho rho f
  invFun f := (Representation.RepMap.equivLinearMapAsModule rho rho).symm f
  left_inv f := (Representation.RepMap.equivLinearMapAsModule rho rho).symm_apply_apply f
  right_inv f := (Representation.RepMap.equivLinearMapAsModule rho rho).apply_symm_apply f
  map_mul' f g := by
    ext x
    rfl
  map_add' f g := by
    ext x
    rfl
  commutes' a := by
    ext x
    rfl
/-- A representation equivalence transports its representation endomorphism algebra by conjugation. -/
public noncomputable def repEndAlgEquivOfRepEquiv
    {F : Type v} [CommRing F] {G : Type u} [Monoid G]
    {V W : Type u} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    {rho : Representation F G V} {sigma : Representation F G W}
    (e : rho ≃ₗ sigma) : Representation.End rho ≃ₐ[F] Representation.End sigma where
  toFun f := e.toRepMap.comp (f.comp e.symm.toRepMap)
  invFun f := e.symm.toRepMap.comp (f.comp e.toRepMap)
  left_inv f := by
    ext x
    simp [Representation.RepMap.comp_apply]
  right_inv f := by
    ext x
    simp [Representation.RepMap.comp_apply]
  map_mul' f g := by
    ext x
    simp [Representation.End.mul_apply, Representation.RepMap.comp_apply]
  map_add' f g := by
    ext x
    simp [Representation.RepMap.comp_apply]
  commutes' a := by
    ext x
    change e.toLinearEquiv (a • e.symm.toLinearEquiv x) = a • x
    rw [e.toLinearEquiv.map_smul]
    exact congrArg (a • ·) (e.apply_symm_apply x)

/-- Conjugating the acting normal subgroup only reindexes its representation endomorphism algebra. -/
public noncomputable def conjugateRepEndAlgEquiv
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) (g : G) :
    Representation.End (Representation.conjugateRep rho g) ≃ₐ[F]
      Representation.End rho where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' h := by
      ext v
      let k : H := ⟨g⁻¹ * h * g, by
        simpa using (inferInstance : H.Normal).conj_mem (h : G) h.2 g⁻¹⟩
      simpa [k, Representation.conjugateRep_apply, mul_assoc] using
        Representation.IntertwiningMap.isIntertwining
          (ρ := Representation.conjugateRep rho g)
          (σ := Representation.conjugateRep rho g) f k v }
  invFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' h := by
      ext v
      simpa [Representation.conjugateRep_apply] using
        Representation.IntertwiningMap.isIntertwining
          (ρ := rho) (σ := rho) f
          ⟨g * (h : G) * g⁻¹,
            (inferInstance : H.Normal).conj_mem (h : G) h.2 g⟩ v }
  left_inv f := rfl
  right_inv f := rfl
  map_mul' f h := rfl
  map_add' f h := rfl
  commutes' a := rfl

public noncomputable def conjugacyEndAlgAut
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) (g : G)
    (e : rho ≃ₗ Representation.conjugateRep rho g) :
    Representation.End rho ≃ₐ[F] Representation.End rho :=
  (repEndAlgEquivOfRepEquiv e).trans (conjugateRepEndAlgEquiv rho g)

public theorem conjugacyEndAlgAut_eq_of_commute
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) (g : G)
    (e e' : rho ≃ₗ Representation.conjugateRep rho g)
    (hcomm : ∀ f d : Representation.End rho, f.comp d = d.comp f) :
    conjugacyEndAlgAut rho g e = conjugacyEndAlgAut rho g e' := by
  ext f x
  change e (f (e.symm x)) = e' (f (e'.symm x))
  let d : Representation.End rho := e.symm.toRepMap.comp e'.toRepMap
  have hd := congrArg (fun q : Representation.End rho => q (e'.symm x)) (hcomm f d)
  calc
    e (f (e.symm x)) = e (f (e.symm (e' (e'.symm x)))) := by simp
    _ = e (f (d (e'.symm x))) := rfl
    _ = e (d (f (e'.symm x))) := by exact congrArg e hd
    _ = e' (f (e'.symm x)) := by simp [d]

public theorem conjugacyEndAlgAut_one
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) :
    conjugacyEndAlgAut rho (1 : G) (conjugateRep_equiv_one rho) = 1 := by
  ext f x
  rfl

public theorem conjugacyEndAlgAut_mul
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) (a b : G)
    (ea : rho ≃ₗ Representation.conjugateRep rho a)
    (eb : rho ≃ₗ Representation.conjugateRep rho b) :
    conjugacyEndAlgAut rho (a * b)
        (eb.trans (conjugateRep_equiv_mul_left rho (g := b) ea)) =
      conjugacyEndAlgAut rho a ea * conjugacyEndAlgAut rho b eb := by
  ext f x
  rfl

public noncomputable def inertiaEndAlgAut
    {F : Type v} [Field F] {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V)
    (g : representationInertiaSubgroup H rho) :
    Representation.End rho ≃ₐ[F] Representation.End rho :=
  conjugacyEndAlgAut rho g (Classical.choice g.property)

/-- The choice-independent conjugation action of the inertia subgroup on the
endomorphism algebra of the represented normal subgroup. -/
public noncomputable def inertiaEndAlgAutHom
    {F : Type v} [Field F] {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V)
    (hcomm : ∀ f d : Representation.End rho, f.comp d = d.comp f) :
    representationInertiaSubgroup H rho →*
      (Representation.End rho ≃ₐ[F] Representation.End rho) where
  toFun := inertiaEndAlgAut H rho
  map_one' := by
    let e : rho ≃ₗ Representation.conjugateRep rho (1 : G) :=
      Classical.choice ((1 : representationInertiaSubgroup H rho).property)
    change conjugacyEndAlgAut rho (1 : G) e = 1
    calc
      conjugacyEndAlgAut rho (1 : G) e =
          conjugacyEndAlgAut rho (1 : G) (conjugateRep_equiv_one rho) :=
        conjugacyEndAlgAut_eq_of_commute rho 1 e (conjugateRep_equiv_one rho) hcomm
      _ = 1 := conjugacyEndAlgAut_one rho
  map_mul' a b := by
    let ea : rho ≃ₗ Representation.conjugateRep rho (a : G) :=
      Classical.choice a.property
    let eb : rho ≃ₗ Representation.conjugateRep rho (b : G) :=
      Classical.choice b.property
    let eab : rho ≃ₗ Representation.conjugateRep rho
        ((a * b : representationInertiaSubgroup H rho) : G) :=
      Classical.choice (a * b).property
    change conjugacyEndAlgAut rho ((a : G) * (b : G)) eab =
      conjugacyEndAlgAut rho (a : G) ea * conjugacyEndAlgAut rho (b : G) eb
    calc
      conjugacyEndAlgAut rho ((a : G) * (b : G)) eab =
          conjugacyEndAlgAut rho ((a : G) * (b : G))
            (eb.trans (conjugateRep_equiv_mul_left rho (g := (b : G)) ea)) :=
        conjugacyEndAlgAut_eq_of_commute rho _ eab _ hcomm
      _ = conjugacyEndAlgAut rho (a : G) ea * conjugacyEndAlgAut rho (b : G) eb :=
        conjugacyEndAlgAut_mul rho (a : G) (b : G) ea eb


/-- Transport the inertia action from intertwining endomorphisms to the
endomorphism algebra of the corresponding group-algebra module. -/
public noncomputable def inertiaModuleEndAlgAutHom
    {F : Type v} [Field F] {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V)
    (hcomm : ∀ f d : Representation.End rho, f.comp d = d.comp f) :
    representationInertiaSubgroup H rho →*
      (Module.End (MonoidAlgebra F H) rho.asModule ≃ₐ[F]
        Module.End (MonoidAlgebra F H) rho.asModule) :=
  (AlgEquiv.autCongr (repEndAlgEquivModuleEnd rho)).toMonoidHom.comp
    (inertiaEndAlgAutHom H rho hcomm)
/-- The conjugation action of the inertia subgroup on the representation
endomorphism algebra. -/
@[reducible] public noncomputable def inertiaEndMulSemiringAction
    {F : Type v} [Field F] {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V)
    (hcomm : ∀ f d : Representation.End rho, f.comp d = d.comp f) :
    MulSemiringAction (representationInertiaSubgroup H rho)
      (Representation.End rho) :=
  MulSemiringAction.compHom (Representation.End rho)
    (inertiaEndAlgAutHom H rho hcomm)

end PFAppendixIV
end BenderSuzuki
