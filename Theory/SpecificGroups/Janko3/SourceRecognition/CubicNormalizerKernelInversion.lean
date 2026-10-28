module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerModelPair

/-!
# Cubic-kernel inversion and a pair-fixing correction

In the actual model C₃ : PGL₂(9), inversion on the cubic kernel extends
while fixing the entire projective complement pointwise. On the preimage
of a subgroup centralized by an outer projective element t, it agrees with
conjugation by t. Their difference therefore fixes that entire preimage
pointwise while conjugating subgroups of the complement by the same t.

This supplies the orientation correction for the third overlap of the J₃
amalgam. It neither assumes nor asserts a global compatible-amalgam marking.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
open Subgroup

/-- Invert the cubic kernel and fix the literal projective complement. -/
@[expose] def kernelInversion : MulAut Model :=
  SemidirectProduct.congr inversion (MulEquiv.refl P) (by
    intro p
    apply MulEquiv.ext
    intro z
    exact (map_inv (action p) z).symm)

theorem kernelInversion_apply (x : Model) :
    kernelInversion x = ⟨x.left⁻¹,x.right⟩ := rfl

theorem kernelInversion_inr (p : P) :
    kernelInversion (SemidirectProduct.inr p) = SemidirectProduct.inr p := by
  apply SemidirectProduct.ext
  · exact inv_one
  · rfl

theorem kernelInversion_inl (z : Z) :
    kernelInversion (SemidirectProduct.inl z) = SemidirectProduct.inl z⁻¹ := rfl

theorem kernelInversion_projection (x : Model) :
    projection (kernelInversion x) = projection x := rfl

/-- Every full preimage, in particular the canonical order-sixty pair,
is preserved by the cubic-only inversion. -/
theorem kernelInversion_preimage (Q : Subgroup P) :
    (Q.comap projection).map kernelInversion.toMonoidHom = Q.comap projection := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hx
  · intro x hx
    refine ⟨kernelInversion x,hx,?_⟩
    apply SemidirectProduct.ext
    · exact inv_inv x.left
    · rfl

/-- On the indicated full preimage, cubic inversion is precisely the
inner automorphism defined by the same outer complement element. -/
theorem kernelInversion_eq_conj_on_preimage (Q : Subgroup P) (t : P)
    (ht : t ∉ derived) (htQ : t ∈ centralizer (Q : Set P))
    (x : Model) (hx : x ∈ Q.comap projection) :
    kernelInversion x = MulAut.conj (SemidirectProduct.inr t : Model) x := by
  have hact : action t = inversion := by simp only [action_apply,if_neg ht]
  have hc : t * x.right * t⁻¹ = x.right := by
    have hh := htQ x.right hx
    rw [← hh,mul_inv_cancel_right]
  apply SemidirectProduct.ext
  · change x.left⁻¹ = ((SemidirectProduct.inr t : Model) * x *
      (SemidirectProduct.inr t : Model)⁻¹).left
    simp [SemidirectProduct.mul_left,hact]
    rfl
  · change x.right = t * x.right * t⁻¹
    exact hc.symm

/-- The correction fixes a full pair preimage pointwise and acts on the
literal projective complement by conjugation with t. -/
theorem exists_pair_fixing_complement_correction (Q : Subgroup P) (t : P)
    (ht : t ∉ derived) (htQ : t ∈ centralizer (Q : Set P)) :
    ∃ τ : MulAut Model,
      (∀ x ∈ Q.comap projection, τ x = x) ∧
      (∀ p : P, τ (SemidirectProduct.inr p) = SemidirectProduct.inr (t*p*t⁻¹)) ∧
      (∀ z : Z, τ (SemidirectProduct.inl z) = SemidirectProduct.inl z) := by
  let τ : MulAut Model := kernelInversion.symm * MulAut.conj (SemidirectProduct.inr t)
  refine ⟨τ,?_,?_,?_⟩
  · intro x hx
    change kernelInversion.symm (MulAut.conj (SemidirectProduct.inr t : Model) x) = x
    rw [←kernelInversion_eq_conj_on_preimage Q t ht htQ x hx]
    exact kernelInversion.symm_apply_apply x
  · intro p
    change kernelInversion.symm ((SemidirectProduct.inr t : Model) *
      SemidirectProduct.inr p * (SemidirectProduct.inr t : Model)⁻¹) = _
    rw [←map_inv,←map_mul,←map_mul]
    exact kernelInversion.injective (by rw [kernelInversion.apply_symm_apply,kernelInversion_inr])
  · intro z
    change kernelInversion.symm (MulAut.conj (SemidirectProduct.inr t : Model)
      (SemidirectProduct.inl z)) = _
    have hx : (SemidirectProduct.inl z : Model) ∈ Q.comap projection := Q.one_mem
    rw [←kernelInversion_eq_conj_on_preimage Q t ht htQ _ hx]
    exact kernelInversion.symm_apply_apply _

end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
