module
public import Theory.Representation.SL2NaturalCommonQuotient

/-!
# Simple images of a natural central cover

Let two maps from a common group have images in a natural SL₂-plane and
in an irreducible noncentral abelian group. Compatible lifts intertwine
both actions. If the natural kernel has pointwise fixed image, then the
second image is the same marked natural module. The equivalence preserves
both original maps, rather than just the isomorphism type.

The fixed subgroup of an irreducible noncentral action is trivial. The
common-image theorem therefore removes the central kernel and supplies the
marked equivalence. Invariant subgroups may be used as the common domain;
the Chapter 11 consumer applies this to every noncentral simple subquotient
of its original cubic-fixed chief section.

Source: Aschbacher--Smith, 11.1.2, printed pp.763--764.
-/

open Subgroup Matrix
open scoped MatrixGroups
namespace QuotientGroup.CommonImage
@[expose] public noncomputable section
variable {M C H F : Type*} [Group M] [CommGroup C] [Group H] [Field F]

/-- Every noncentral irreducible common image is the same marked natural
plane, provided the original natural kernel has pointwise fixed image.
The compatible lifts allow M to be any invariant subgroup upstairs. -/
theorem natural_simple_common_image
    (p : M →* Multiplicative (Fin 2 → F)) (q : M →* C)
    (hq : Function.Surjective q) (r : H →* SL(2,F)) (hr : Function.Surjective r)
    (τ : H →* MulAut C)
    (hlift : ∀ h x, ∃ y, q y = τ h (q x) ∧
      p y = Matrix.SL2.naturalAction F (r h) (p x))
    (hcentral : ∀ x, p x = 1 → ∀ h, τ h (q x) = q x)
    (hirr : ∀ P : Subgroup C, (∀ h x, x ∈ P → τ h x ∈ P) → P = ⊥ ∨ P = ⊤)
    (hmove : ∃ h x, τ h x ≠ x) :
    ∃ e : C ≃* Multiplicative (Fin 2 → F),
      (∀ x, e (q x) = p x) ∧
      ∀ h x, e (τ h x) = Matrix.SL2.naturalAction F (r h) (e x) := by
  let R : Subgroup C :=
    { carrier := {x | ∀ h, τ h x = x}
      one_mem' := fun h => map_one _
      mul_mem' := by intro x y hx hy h; rw [map_mul,hx h,hy h]
      inv_mem' := by intro x hx h; rw [map_inv,hx h] }
  have hR : R = ⊥ := by
    obtain hh | hh := hirr R (fun h x hx => by change ∀ k, τ k (τ h x) = τ h x; rw [hx h]; exact hx)
    · exact hh
    · obtain ⟨h,x,hx⟩ := hmove
      exact (hx (hh.ge (mem_top x) h)).elim
  have hZ : kernelImage p q = ⊥ := by
    apply bot_unique
    rintro _ ⟨x,hx,rfl⟩
    exact hR.le (hcentral x hx)
  obtain ht | ⟨e,he⟩ := natural_quotient_dichotomy p q hq r hr
    (fun h x => by obtain ⟨y,_,hy⟩ := hlift h x; exact ⟨y,hy⟩)
    (fun h x hx => by
      obtain ⟨y,hy,hpy⟩ := hlift h x
      exact ⟨y,by rw [hy,hx,map_one],hpy⟩)
  · obtain ⟨h,x,hx⟩ := hmove
    have hx1 : x = 1 := (ht.symm.trans hZ).le (mem_top x)
    exact (hx (by rw [hx1,map_one])).elim
  let f : C ≃* C ⧸ kernelImage p q := MulEquiv.ofBijective
    (QuotientGroup.mk' (kernelImage p q))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',hZ]),
      QuotientGroup.mk'_surjective _⟩
  refine ⟨f.trans e,he,?_⟩
  intro h x
  obtain ⟨a,rfl⟩ := hq x
  obtain ⟨b,hb,hp⟩ := hlift h a
  change e (QuotientGroup.mk' _ (τ h (q a))) = _
  rw [←hb,he b]
  exact hp.trans (congrArg (Matrix.SL2.naturalAction F (r h)) (he a).symm)

end
end QuotientGroup.CommonImage
