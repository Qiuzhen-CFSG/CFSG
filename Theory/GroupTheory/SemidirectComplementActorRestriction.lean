module
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Using the actual complement as a semidirect actor

Suppose H is the product of a normal subgroup L and a complement E. A
homomorphism into Q semidirect A has prescribed linear values φ on L and
coefficient values c on E. Then those same linear values extend to a map
into Q semidirect E, where E acts through the original coefficient map c;
the new map sends each e in E to that actual actor e. No finiteness or
injectivity hypothesis is required.

The original homomorphism equations identify conjugation by E on L with
the action of c(E) after applying φ. Use the actual complement equivalence
between H and L semidirect E, then apply the semidirect map induced by φ
and the identity on E. Its values on the linear and actor factors follow
from the defining equations of those two homomorphisms.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp27–28.
This generic restriction lets the final odd-action lift use the original
complement as its coefficient actor, while retaining the supplied
projective linear and coefficient equations.
-/

namespace Subgroup

/-- Replace the coefficient actor by the actual complement while preserving
the original projective linear values and the complement coordinates. -/
public theorem exists_semidirect_hom_with_complement_actor
    {H Q A : Type*} [Group H] [Group Q] [Group A]
    (L E : Subgroup H) [L.Normal] (hcomp : L.IsComplement' E)
    (β : A →* MulAut Q) (f : H →* Q ⋊[β] A)
    (φ : L →* Q) (c : E →* A)
    (hfL : ∀ l : L, f l = SemidirectProduct.inl (φ l))
    (hfE : ∀ e : E, f e = SemidirectProduct.inr (c e)) :
    ∃ fE : H →* Q ⋊[β.comp c] E,
      (∀ l : L, fE l = SemidirectProduct.inl (φ l)) ∧
      (∀ e : E, fE e = SemidirectProduct.inr e) := by
  let γ : E →* MulAut L :=
    L.normalizerMonoidHom.comp (inclusion (L.normalizer_eq_top ▸ le_top))
  have hγ (e : E) (l : L) : (γ e l : H) = e * l * (e : H)⁻¹ := rfl
  have hagree (e : E) : φ.comp (γ e).toMonoidHom =
      ((β.comp c) ((MonoidHom.id E) e)).toMonoidHom.comp φ := by
    ext l
    change φ (γ e l) = β (c e) (φ l)
    apply SemidirectProduct.inl_injective (φ := β)
    rw [← hfL, hγ, map_mul, map_mul, map_inv, hfL, hfE]
    simpa using (SemidirectProduct.inl_aut (φ := β) (c e) (φ l)).symm
  let k := SemidirectProduct.mulEquivSubgroup hcomp
  let m : L ⋊[γ] E →* Q ⋊[β.comp c] E := SemidirectProduct.map φ (MonoidHom.id E) hagree
  refine ⟨m.comp k.symm.toMonoidHom, ?_, ?_⟩
  · intro l
    have hk : k.symm l = SemidirectProduct.inl l := by
      apply k.injective
      rw [k.apply_symm_apply]
      simp [k]
    change m (k.symm l) = _
    rw [hk]
    exact SemidirectProduct.map_inl _ _ _ _
  · intro e
    have hk : k.symm e = SemidirectProduct.inr e := by
      apply k.injective
      rw [k.apply_symm_apply]
      simp [k]
    change m (k.symm e) = _
    rw [hk]
    exact SemidirectProduct.map_inr _ _ _ _
end Subgroup
