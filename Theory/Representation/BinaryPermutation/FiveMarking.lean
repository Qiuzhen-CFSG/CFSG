module
public import Theory.Representation.BinaryPermutation
public import Theory.SpecificGroups.Symmetric.InnerAutomorphisms

/-!
# Natural five-point coordinates with a prescribed quotient map

Two surjections onto S₅ with the same kernel differ by an automorphism of
S₅. Every such automorphism is inner. Applying the inverse conjugating
permutation to the natural module therefore changes the coordinates to
use the prescribed surjection, without changing the representation.

Source: the inner-automorphism theorem for S₅, deduced from GLS3,
Theorem 5.2.1 in Theory.SpecificGroups.Symmetric.InnerAutomorphisms.
-/

public noncomputable section
open Subgroup Representation

namespace BinaryPermutation

/-- Natural five-point coordinates can use any prescribed surjection having
exactly the action kernel. -/
theorem natural_five_coordinates_of_kernel
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (q f : D →* Equiv.Perm (Fin 5))
    (hq : Function.Surjective q) (hf : Function.Surjective f) (hk : q.ker = f.ker)
    (c : W ≃ₗ[ZMod 2] natural (Fin 5))
    (hc : ∀ g v, c (ρ g v) = naturalRepresentation (Fin 5) (f g) (c v)) :
    ∃ d : W ≃ₗ[ZMod 2] natural (Fin 5), ∀ g v,
      d (ρ g v) = naturalRepresentation (Fin 5) (q g) (d v) := by
  let eq := QuotientGroup.liftEquiv q.ker hq rfl
  let ef := QuotientGroup.liftEquiv q.ker hf hk
  obtain ⟨p,hp⟩ := Equiv.Perm.conj_surjective_of_degree (by decide : 5 ≤ 5)
    (by decide) (eq.symm.trans ef)
  have hfg (g : D) : f g = p * q g * p⁻¹ := by
    have ha := MulEquiv.congr_fun hp (q g)
    change p * q g * p⁻¹ = ef (eq.symm (q g)) at ha
    have hqg : eq.symm (q g) = (g : D ⧸ q.ker) := by
      apply eq.injective
      simp only [MulEquiv.apply_symm_apply]
      rfl
    rw [hqg] at ha
    exact ha.symm
  let σ := naturalRepresentation (Fin 5)
  let a : natural (Fin 5) ≃ₗ[ZMod 2] natural (Fin 5) := {
    toLinearMap := σ p⁻¹
    invFun := σ p
    left_inv := by
      intro v
      change (σ p * σ p⁻¹) v = v
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl
    right_inv := by
      intro v
      change (σ p⁻¹ * σ p) v = v
      rw [←map_mul,inv_mul_cancel,map_one]
      rfl }

  refine ⟨c.trans a,?_⟩
  intro g v
  change σ p⁻¹ (c (ρ g v)) = σ (q g) (σ p⁻¹ (c v))
  rw [hc]
  rw [←Module.End.mul_apply,←Module.End.mul_apply,←map_mul,←map_mul,hfg]
  simp only [inv_mul_cancel_left,mul_assoc]

end BinaryPermutation
