module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Basic

/-!
# Faithful extensions of the marked natural A₆ action

Conjugate the given faithful action by its prescribed module equivalence.
Normality places its image in the normalizer of the alternating image. Once
that normalizer is identified with the symmetric image, the action gives a
faithful permutation embedding extending the given identification of `K`.
The index-two property then yields a genuine A₆ or S₆ isomorphism.

The normalizer equality is an explicit remaining intrinsic premise in this
module, not an asserted conclusion. The group and module compatibilities are
retained in the result. Source: Aschbacher–Smith 13.8.27(1a), printed p.963.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix

open BinaryPermutation

private theorem overgroup_alternating (J : Subgroup Symmetric)
    (hJ : alternatingGroup (Fin 6) ≤ J) : J = alternatingGroup (Fin 6) ∨ J = ⊤ := by
  classical
  by_cases h : J ≤ alternatingGroup (Fin 6)
  · exact Or.inl (le_antisymm h hJ)
  · right
    obtain ⟨s, hs, hsa⟩ := SetLike.not_le_iff_exists.mp h
    apply top_unique
    intro g _
    by_cases hga : g ∈ alternatingGroup (Fin 6)
    · exact hJ hga
    · have hx : g * s⁻¹ ∈ alternatingGroup (Fin 6) := by
        rw [Subgroup.mul_mem_iff_of_index_two alternatingGroup.index_eq_two,
          Subgroup.inv_mem_iff]
        simp [hga, hsa]
      simpa only [inv_mul_cancel_right] using J.mul_mem (hJ hx) hs

/-- An actual permutation embedding containing the alternating group determines
an actual alternating or symmetric isomorphism, with its embedding retained. -/
theorem extension_equiv_of_embedding {H : Type*} [Group H]
    (f : H →* Symmetric) (hf : Function.Injective f)
    (ha : alternatingGroup (Fin 6) ≤ f.range) :
    (∃ e : H ≃* Alternating, ∀ h, (e h).val = f h) ∨
      (∃ e : H ≃* Symmetric, ∀ h, e h = f h) := by
  rcases overgroup_alternating f.range ha with h | h
  · exact Or.inl ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr h),
      fun _ => rfl⟩
  · exact Or.inr ⟨(MonoidHom.ofInjective hf).trans
      ((MulEquiv.subgroupCongr h).trans (Subgroup.topEquiv)), fun _ => rfl⟩

/-- The extension deduction with the intrinsic normalizer calculation explicit.
The returned embedding preserves both the prescribed restriction to `K` and
the complete action on `U`. The normalizer premise remains to be discharged. -/
theorem faithful_extension_of_normalizer
    (hN : Subgroup.normalizer (alternatingImage : Set LinearGroup) = symmetricImage)
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (K : Subgroup H) [K.Normal]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (eK : K ≃* Alternating) (E : U ≃ₗ[ZMod 2] Natural)
    (he : ∀ k : K, ∀ u, E (ρ k u) = alternatingAction (eK k) (E u)) :
    ∃ f : H →* Symmetric, Function.Injective f ∧
      (∀ k : K, f k = (eK k).val) ∧
      (∀ h u, E (ρ h u) = symmetricAction (f h) (E u)) ∧
      ((∃ e : H ≃* Alternating, ∀ h, (e h).val = f h) ∨
        (∃ e : H ≃* Symmetric, ∀ h, e h = f h)) := by
  let c := LinearMap.GeneralLinearGroup.congrLinearEquiv E
  let γ : H →* LinearGroup := c.toMonoidHom.comp ρ.asGroupHom
  have hγ : Function.Injective γ := by
    intro a b hab
    apply hρ
    exact congrArg Units.val (c.injective hab)
  have hγK (k : K) : γ k = alternatingHom (eK k) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change E (ρ k (E.symm v)) = alternatingAction (eK k) v
    simpa using he k (E.symm v)
  have hmap : K.map γ = alternatingImage := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨eK ⟨k, hk⟩, (hγK ⟨k, hk⟩).symm⟩
    · rintro _ ⟨k, rfl⟩
      obtain ⟨j, rfl⟩ := eK.surjective k
      exact ⟨j.val, j.property, hγK j⟩
  have hγmem (h : H) : γ h ∈ symmetricImage := by
    rw [← hN, ← hmap]
    apply K.le_normalizer_map γ
    exact ⟨h, by rw [K.normalizer_eq_top]; trivial, rfl⟩
  let γ' : H →* symmetricImage := γ.codRestrict symmetricImage hγmem
  let eS : Symmetric ≃* symmetricImage := MonoidHom.ofInjective symmetricHom_injective
  let f : H →* Symmetric := eS.symm.toMonoidHom.comp γ'
  have hsf (h : H) : symmetricHom (f h) = γ h := by
    exact congrArg Subtype.val (eS.apply_symm_apply (γ' h))
  have hf : Function.Injective f := by
    intro a b hab
    apply hγ
    rw [← hsf, ← hsf, hab]
  have hfK (k : K) : f k = (eK k).val := by
    apply symmetricHom_injective
    rw [hsf, hγK]
    rfl
  have hact (h : H) (u : U) : E (ρ h u) = symmetricAction (f h) (E u) := by
    have hh := congrArg (fun l : LinearGroup => l.val (E u)) (hsf h)
    change symmetricAction (f h) (E u) = E (ρ h (E.symm (E u))) at hh
    simpa using hh.symm
  refine ⟨f, hf, hfK, hact, extension_equiv_of_embedding f hf ?_⟩
  intro a ha
  obtain ⟨k, hk⟩ := eK.surjective ⟨a, ha⟩
  exact ⟨k.val, by rw [hfK, hk]⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
