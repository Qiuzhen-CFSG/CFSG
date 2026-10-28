module
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Linear complements in subgroups of the special affine plane

A subgroup projecting onto SL₂ either has trivial translation kernel or
contains every translation, by additive irreducibility of the natural plane.
In the first case projection is an isomorphism; in the second case the subgroup
is the full affine group. Both cases construct a section of the literal
linear-part map, and hence an SL₂ embedding in any faithfully marked subgroup.

This supports the torus-centralizer construction in Aschbacher--Smith,
original 4.3.12, printed p.617, using the affine local model F.1.12(I).
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SL2
variable {F : Type*} [Field F]

/-- A surjective linear-part map on an affine subgroup has an actual section. -/
theorem subgroup_section_of_linear_surjective (C : Subgroup (Affine F))
    (hs : Function.Surjective ((SemidirectProduct.rightHom : Affine F →* SL(2,F)).comp C.subtype)) :
    ∃ j : SL(2,F) →* C, ∀ a, (j a).val.right = a := by
  let f := (SemidirectProduct.rightHom : Affine F →* SL(2,F)).comp C.subtype
  let V := C.comap (SemidirectProduct.inl : Multiplicative (Fin 2 → F) →* Affine F)
  have hi : ∀ g v, v ∈ V → naturalAction F g v ∈ V := by
    intro g v hv
    obtain ⟨k,hk⟩ := hs g
    change SemidirectProduct.inl (naturalAction F g v) ∈ C
    change k.val.right = g at hk
    rw [←hk,←conjugate_inl]
    exact C.mul_mem (C.mul_mem k.property hv) (C.inv_mem k.property)
  rcases naturalAction_irreducible F V hi with hb | ht
  · have hf : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro x hx
      have hxr : x.val.right = 1 := hx
      have hxl : x.val.left ∈ V := by
        change SemidirectProduct.inl x.val.left ∈ C
        have he : SemidirectProduct.inl x.val.left = x.val := by
          apply SemidirectProduct.ext
          · rfl
          · exact hxr.symm
        rw [he]
        exact x.property
      have hleft : x.val.left = 1 := mem_bot.mp (hb ▸ hxl)
      apply mem_bot.mpr
      apply Subtype.ext
      exact SemidirectProduct.ext hleft hxr
    let e := MulEquiv.ofBijective f ⟨hf,hs⟩
    exact ⟨e.symm.toMonoidHom,fun a => e.apply_symm_apply a⟩
  · have hinr (a : SL(2,F)) : (SemidirectProduct.inr a : Affine F) ∈ C := by
      obtain ⟨k,hk⟩ := hs a
      have hv : k.val.left ∈ V := ht ▸ mem_top _
      have hh := C.mul_mem (C.inv_mem hv) k.property
      have he : (SemidirectProduct.inl k.val.left)⁻¹ * k.val = SemidirectProduct.inr a := by
        apply SemidirectProduct.ext
        · simp
        · simpa using hk
      rwa [he] at hh
    exact ⟨SemidirectProduct.inr.codRestrict C hinr,fun _ => rfl⟩

/-- A faithful affine marking with full linear part contains a copy of SL₂. -/
theorem embedding_of_affine_projection_surjective {A : Type*} [Group A]
    (f : A →* Affine F) (hf : Function.Injective f)
    (hs : Function.Surjective ((SemidirectProduct.rightHom : Affine F →* SL(2,F)).comp f)) :
    ∃ j : SL(2,F) →* A, Function.Injective j := by
  let e := MonoidHom.ofInjective hf
  have hsurj : Function.Surjective
      ((SemidirectProduct.rightHom : Affine F →* SL(2,F)).comp f.range.subtype) := by
    intro a
    obtain ⟨x,hx⟩ := hs a
    exact ⟨e x,hx⟩
  obtain ⟨j,hj⟩ := subgroup_section_of_linear_surjective f.range hsurj
  refine ⟨e.symm.toMonoidHom.comp j, e.symm.injective.comp ?_⟩
  intro a b hab
  exact (hj a).symm.trans ((congrArg (fun x : f.range => x.val.right) hab).trans (hj b))
end Matrix.SL2
