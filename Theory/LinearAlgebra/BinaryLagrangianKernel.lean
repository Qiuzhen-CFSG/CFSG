module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Theory.ElementaryAbelian.Basic

/-!
# Pointwise kernels on binary Lagrangians

An isometry fixing a self-orthogonal subspace pointwise has displacement
in that subspace. Its displacement therefore squares to zero, so the
isometry squares to one. A faithful group of such isometries is elementary
abelian. No dimension, nondegeneracy or transitivity premise is needed.

This is the linear algebra behind the elementary plane core in
Aschbacher–Smith 13.4.9, printed p.906. The C₃ application retains the
Lagrangian spanned by the original seven incident points.
-/

public section

namespace Theory.LinearAlgebra
variable {V H : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Group H]

/-- The displacement lies in the same subspace fixed pointwise. -/
theorem binary_lagrangian_displacement
    (B : LinearMap.BilinForm (ZMod 2) V)
    (W : Submodule (ZMod 2) V) (hW : B.orthogonal W = W)
    (c : V ≃ₗ[ZMod 2] V) (hc : ∀ x y, B (c x) (c y) = B x y)
    (hfix : ∀ w ∈ W, c w = w) (x : V) : c x - x ∈ W := by
  rw [← hW]
  intro w hw
  have h := hc w x
  rw [hfix w hw] at h
  rw [map_sub, h, sub_self]

/-- A faithful binary Lagrangian pointwise kernel is elementary abelian. -/
theorem binary_lagrangian_kernel_isElementaryAbelian
    (B : LinearMap.BilinForm (ZMod 2) V)
    (W : Submodule (ZMod 2) V) (hW : B.orthogonal W = W)
    (ρ : H →* (V ≃ₗ[ZMod 2] V)) (hf : Function.Injective ρ)
    (hρ : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (hfix : ∀ g w, w ∈ W → ρ g w = w) : IsElementaryAbelian 2 H := by
  have hsq (g : H) : g ^ 2 = 1 := by
    apply hf
    rw [map_pow, map_one, pow_two]
    ext x
    change ρ g (ρ g x) = x
    have hh := hfix g (ρ g x - x)
      (binary_lagrangian_displacement B W hW (ρ g) (hρ g) (hfix g) x)
    rw [map_sub] at hh
    calc
      ρ g (ρ g x) = (ρ g x - x) + ρ g x := sub_eq_iff_eq_add.mp hh
      _ = x := by
        rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (ZModModule.add_self x),
          add_comm (ρ g x) x, add_assoc, ZModModule.add_self, add_zero]
  have hinv (g : H) : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using hsq g)
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  calc
    a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv, hinv]

end Theory.LinearAlgebra
