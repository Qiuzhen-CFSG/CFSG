module

public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Group

/-!
# Uniqueness of lifts from p-perfect groups

Two homomorphisms from a p-perfect group which agree after a projection
with central p-group kernel agree already upstairs. Their pointwise
quotient is a homomorphism into the kernel, and p-perfection kills it.
This is the central-kernel rigidity step used in Aschbacher--Smith C.1.10,
printed p.124. Neither finiteness nor surjectivity is needed.
-/

public section
open Subgroup

theorem IsPPerfect.hom_eq_of_comp_eq_of_central_pGroup_kernel {L M B : Type*} [Group L] [Group M] [Group B]
    {p : ℕ} [Fact p.Prime] (hL : IsPPerfect p L)
    (g : M →* B) (hc : g.ker ≤ center M) (hp : IsPGroup p g.ker)
    (f₁ f₂ : L →* M) (he : g.comp f₁ = g.comp f₂) : f₁ = f₂ := by
  have hm (x : L) : f₁ x * (f₂ x)⁻¹ ∈ g.ker := by
    have hx := DFunLike.congr_fun he x
    change g (f₁ x) = g (f₂ x) at hx
    simp [MonoidHom.mem_ker, hx]
  let d : L →* g.ker := {
    toFun x := ⟨f₁ x * (f₂ x)⁻¹, hm x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change f₁ (x * y) * (f₂ (x * y))⁻¹ =
        (f₁ x * (f₂ x)⁻¹) * (f₁ y * (f₂ y)⁻¹)
      have hy := mem_center_iff.mp (hc (hm y)) (f₂ x)⁻¹
      rw [map_mul, map_mul, mul_inv_rev]
      calc
        _ = f₁ x * ((f₁ y * (f₂ y)⁻¹) * (f₂ x)⁻¹) := by group
        _ = f₁ x * ((f₂ x)⁻¹ * (f₁ y * (f₂ y)⁻¹)) := by rw [hy]
        _ = _ := by group }
  have hd := hL.hom_eq_one_of_isPGroup hp d
  ext x
  have hx := congrArg (fun k : L →* g.ker => (k x : M)) hd
  exact mul_inv_eq_one.mp hx

