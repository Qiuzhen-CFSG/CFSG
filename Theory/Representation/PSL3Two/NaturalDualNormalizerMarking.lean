module
public import Theory.Representation.PSL3Two.NaturalDualNonFF
public import Theory.Representation.PSL3Two.NaturalDualRank

/-!
# Constructing the automorphism marking of a normal natural--dual component

A full normal component action makes the ambient linear operators normalize
its actual action image. The faithful normalizer map constructs the component
automorphism action. Uniqueness of implementing operators identifies the
ambient representation with the canonical automorphism representation, on
the same vectors and with the same kernel.

Source application: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1041.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDual

/-- The canonical action implements the specified automorphism. -/
theorem autAction_covariance (a : MulAut Group) (g : Group) (v : Space) :
    autAction a (action g v) = action (a g) (autAction a v) := by
  have he : a * MulAut.conj g = MulAut.conj (a g) * a := by
    ext k
    simp only [MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv]
  rw [←autAction_inner,←Module.End.mul_apply,←map_mul,he,map_mul,Module.End.mul_apply,
    autAction_inner]

/-- Covariance identifies the actual implementing operator with the canonical
natural--dual action, without a new choice of module coordinates. -/
theorem eq_autAction_of_covariance {H : Type*} [_root_.Group H]
    (η : Representation (ZMod 2) H Space) (a : H →* MulAut Group)
    (ha : ∀ h g v, η h (action g v) = action (a h g) (η h v)) (h : H) :
    η h = autAction (a h) := by
  exact congrArg LinearEquiv.toLinearMap (implementing_unique (a h)
    (LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom h))
    (LinearMap.GeneralLinearGroup.toLinearEquiv (autAction.asGroupHom (a h)))
    (ha h) (autAction_covariance (a h)))

/-- A full normal component action constructs the ambient automorphism marking
on the same natural--dual space. -/
theorem exists_automorphism_marking {H : Type*} [_root_.Group H]
    (η : Representation (ZMod 2) H Space) (K : Subgroup H) [K.Normal]
    (f : K →* Group) (hf : Function.Surjective f)
    (he : ∀ k : K, η k = action (f k)) :
    ∃ a : H →* MulAut Group, (∀ h, η h = autAction (a h)) ∧
      (∀ h, a h = 1 ↔ η h = 1) := by
  have himage : actionImage (η.comp K.subtype) = actionImage action := by
    ext g
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨f k,Units.ext (he k).symm⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨k,rfl⟩ := hf g
      exact ⟨k,Units.ext (he k)⟩
  have hn : actionImage η ≤ linearNormalizer action := by
    have hh := actionImage_le_linearNormalizer η K
    change actionImage η ≤ normalizer (actionImage (η.comp K.subtype) : Set _) at hh
    rwa [himage] at hh
  let b : H →* linearNormalizer action := η.asGroupHom.codRestrict _
    (fun h => hn ⟨h,rfl⟩)
  let a := normalizerAutomorphism.comp b
  have hc (h : H) (g : Group) (v : Space) :
      η h (action g v) = action (a h g) (η h v) :=
    normalizerAutomorphism_intertwines (b h) g v
  have ha := eq_autAction_of_covariance η a hc
  refine ⟨a,ha,?_⟩
  intro h
  rw [ha,←map_one autAction]
  exact ⟨fun hh => congrArg autAction hh,fun hh => autAction_injective hh⟩
end BinaryLinearThree.NaturalDual
