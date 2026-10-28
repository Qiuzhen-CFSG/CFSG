module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerThirdAlignment

/-!
# Recognize and align an actual full third overlap

The full cubic kernel and the original A₅ intersection with the retained
projective complement identify the whole third overlap as a full preimage.
An order-thirty intersection with the full pair then forces its projective
order-ten intersection to be the canonical derived pair. No quotient
marking or normalizer compatibility is supplied as an extra hypothesis.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
open Subgroup

private def preimageCoordinates (H : Subgroup P) : H.comap projection ≃ Z × H where
  toFun x := (x.val.left,⟨x.val.right,x.property⟩)
  invFun x := ⟨⟨x.1,x.2⟩,x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem projection_image_five (C : Subgroup Model) (hk : projection.ker ≤ C)
    (hfive : Nonempty ((C ⊓ (SemidirectProduct.inr : P →* Model).range : Subgroup Model) ≃*
      alternatingGroup (Fin 5))) :
    Nonempty (C.map projection ≃* alternatingGroup (Fin 5)) := by
  let E := C ⊓ (SemidirectProduct.inr : P →* Model).range
  let f : E →* P := projection.comp E.subtype
  have hf : Function.Injective f := by
    intro x y he
    obtain ⟨p,hp⟩ := x.property.2
    obtain ⟨q,hq⟩ := y.property.2
    apply Subtype.ext
    rw [←hp,←hq]
    apply congrArg SemidirectProduct.inr
    change projection (x : Model) = projection (y : Model) at he
    rw [←hp,←hq] at he
    exact he
  have hr : f.range = C.map projection := by
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      exact mem_map_of_mem projection x.property.1
    · rintro _ ⟨x,hx,rfl⟩
      have hl : (SemidirectProduct.inl x.left : Model) ∈ C := hk (by
        change projection (SemidirectProduct.inl x.left) = 1
        rfl)
      have hi : (SemidirectProduct.inr x.right : Model) ∈ C := by
        have hh := C.mul_mem (C.inv_mem hl) hx
        nth_rw 2 [←SemidirectProduct.inl_left_mul_inr_right x] at hh
        simpa only [inv_mul_cancel_left] using hh
      exact ⟨⟨SemidirectProduct.inr x.right,hi,⟨x.right,rfl⟩⟩,rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hr.symm).trans
    ((MonoidHom.ofInjective hf).symm.trans hfive.some)⟩

/-- Align an actual full third overlap using its full cubic kernel,
literal complement intersection, and full pair intersection. -/
theorem exists_full_third_alignment (C : Subgroup Model)
    (hk : projection.ker ≤ C)
    (hfive : Nonempty ((C ⊓ (SemidirectProduct.inr : P →* Model).range : Subgroup Model) ≃*
      alternatingGroup (Fin 5)))
    (hpair : Nat.card (C ⊓ pair : Subgroup Model) = 30) :
    ∃ τ : MulAut Model,
      (∀ x ∈ pair, τ x = x) ∧
      (∀ x ∈ projection.ker, τ x = x) ∧
      (SemidirectProduct.inr : P →* Model).range.map τ.toMonoidHom =
        (SemidirectProduct.inr : P →* Model).range ∧
      C.map τ.toMonoidHom = thirdOverlap := by
  let H := C.map projection
  have hH : Nonempty (H ≃* alternatingGroup (Fin 5)) := projection_image_five C hk hfive
  have hfull : H.comap projection = C := comap_map_eq_self hk
  have he : (H ⊓ projectivePair).comap projection = C ⊓ pair := by
    rw [comap_inf,hfull]
    rfl
  have hc : Nat.card (H ⊓ projectivePair : Subgroup P) = 10 := by
    have hh := Nat.card_congr (preimageCoordinates (H ⊓ projectivePair))
    rw [he,hpair,Nat.card_prod] at hh
    have hz : Nat.card Z = 3 := by
      simp [Z,Nat.card_eq_fintype_card,Fintype.card_multiplicative]
    rw [hz] at hh
    omega
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective
    (f := hH.some.symm.toMonoidHom) hH.some.symm.surjective
  have hd : H ≤ derived := by
    rw [←H.commutator_eq_self]
    exact commutator_mono le_top le_top
  have hEq : H ⊓ projectivePair = pairTen :=
    eq_of_le_of_card_ge (le_inf inf_le_right (inf_le_left.trans hd))
      (by rw [hc,pairTen_card])
  obtain ⟨τ,hfix,hker,hcomp,hthird⟩ := exists_canonical_third_alignment H hH
    (hEq ▸ inf_le_left)
  exact ⟨τ,hfix,hker,hcomp,hfull ▸ hthird⟩
end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
