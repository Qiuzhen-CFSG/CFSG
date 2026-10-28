module

public import Theory.Representation.SLThreeCentralExtension

/-!
# Normalizers of central covers of the binary natural three-space

A linear automorphism preserving the central kernel of a commutator-generated
cover and normalizing the represented SL₃(2) action already belongs to that
action. Its induced automorphism of the natural quotient is a determinant-one
matrix, since the coefficient field is F₂. Subtracting the corresponding group
action gives a map into the fixed kernel which kills every commutator, hence
vanishes on the whole covering module.

This applies to the indecomposable extension in Aschbacher–Smith, Section 12.4,
printed pp.812–813, and explains the full-normalizer action used with B.4.8.
It does not require the extension to split or its fixed space to vanish.
-/

public section

open Representation Representation.OneCohomology
namespace Representation.OneCohomology.SLThreeCentralExtension
open BinaryLinearThree
variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) Group X}

/-- Every linear normalizer preserving the marked kernel acts as an element
of SL₃(2) on a central cover of its natural module. -/
theorem normalizing_equiv_eq_action
    (p : σ.IntertwiningMap W) (hp : IsCover p)
    (e : X ≃ₗ[ZMod 2] X)
    (heker : ∀ x, p x = 0 → p (e x) = 0)
    (hen : ∀ k, ∃ h, ∀ x, e (σ k x) = σ h (e x)) :
    ∃ g : Group, ∀ x, e x = σ g x := by
  let q := p.toLinearMap
  have hk : q.ker ≤ (q.comp e.toLinearMap).ker := heker
  let b : Vector →ₗ[ZMod 2] Vector :=
    (q.ker.liftQ (q.comp e.toLinearMap) hk).comp
      (q.quotKerEquivOfSurjective hp.1).symm.toLinearMap
  have hb (x : X) : b (p x) = p (e x) := by
    change (q.ker.liftQ (q.comp e.toLinearMap) hk)
      ((q.quotKerEquivOfSurjective hp.1).symm (q x)) = q (e x)
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  have hbs : Function.Surjective b := by
    intro v
    obtain ⟨x, rfl⟩ := hp.1 v
    refine ⟨p (e.symm x), ?_⟩
    rw [hb, e.apply_symm_apply]
  let B : Vector ≃ₗ[ZMod 2] Vector := LinearEquiv.ofBijective b
    ⟨(LinearMap.injective_iff_surjective).mpr hbs, hbs⟩
  have hdet : (LinearMap.toMatrix' B.toLinearMap).det = 1 := by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ B.isUnit_det'.ne_zero
  let g : Group := ⟨LinearMap.toMatrix' B.toLinearMap, hdet⟩
  have hgp (x : X) : W g (p x) = p (e x) := by
    change Matrix.toLin' (LinearMap.toMatrix' B.toLinearMap) (p x) = _
    rw [Matrix.toLin'_toMatrix']
    exact hb x
  let f : X →ₗ[ZMod 2] X := e.toLinearMap - σ g
  have hfix (x : X) : f x ∈ fixed σ := by
    apply hp.2.1
    change p (e x - σ g x) = 0
    rw [map_sub, p.isIntertwining, hgp, sub_self]
  have hzero : Coinvariants.ker σ ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, x⟩, rfl⟩
    obtain ⟨h, hh⟩ := hen k
    have hprod : h * g = g * k := by
      apply Matrix.SpecialLinearGroup.toLin'_injective
      apply LinearEquiv.ext
      intro v
      obtain ⟨y, rfl⟩ := hp.1 v
      change W (h * g) (p y) = W (g * k) (p y)
      simp only [map_mul, Module.End.mul_apply]
      rw [hgp, ← IntertwiningMap.isIntertwining _ _ p h, ← hh, ← hgp, IntertwiningMap.isIntertwining _ _ p k]
    have hprod' : σ g (σ k x) = σ h (σ g x) := by
      simp only [← Module.End.mul_apply, ← map_mul, hprod]
    change f (σ k x - x) = 0
    rw [map_sub]
    change (e (σ k x) - σ g (σ k x)) - f x = 0
    rw [hh, hprod', ← map_sub]
    exact sub_eq_zero.mpr (hfix x h)
  refine ⟨g, fun x => sub_eq_zero.mp ?_⟩
  exact hzero (hp.2.2 ▸ Submodule.mem_top)

end Representation.OneCohomology.SLThreeCentralExtension
