module
public import Theory.GroupTheory.PPerfectCentralLift
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow detection through a central prime-group kernel

Two homomorphisms agreeing modulo a central p-group kernel agree upstairs
when they agree on a Sylow p-subgroup. Their pointwise difference is a
homomorphism into the kernel. Its image is a p-group, whereas its kernel
contains a Sylow subgroup, so the image is trivial.

This is the central-cover lifting used in Aschbacher--Smith, original
15.1.22(**), printed p.1099, without a coprimality assumption on the actor.
-/

public section
open Subgroup
namespace MonoidHom
variable {D E B : Type*} [Group D] [Group E] [Group B] [Finite D] [Finite E]
variable {p : ℕ} [Fact p.Prime]

theorem eq_of_central_pGroup_kernel_of_sylow
    (g : E →* B) (hc : g.ker ≤ center E) (hp : IsPGroup p g.ker)
    (f₁ f₂ : D →* E) (he : g.comp f₁ = g.comp f₂)
    (S : Sylow p D) (hs : ∀ x ∈ S, f₁ x = f₂ x) : f₁ = f₂ := by
  have hm (x : D) : f₁ x * (f₂ x)⁻¹ ∈ g.ker := by
    have hx := DFunLike.congr_fun he x
    change g (f₁ x) = g (f₂ x) at hx
    simp [MonoidHom.mem_ker, hx]
  let d : D →* g.ker := {
    toFun x := ⟨f₁ x * (f₂ x)⁻¹, hm x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change f₁ (x * y) * (f₂ (x * y))⁻¹ =
        (f₁ x * (f₂ x)⁻¹) * (f₁ y * (f₂ y)⁻¹)
      have hy := mem_center_iff.mp (hc (hm y)) (f₂ x)⁻¹
      rw [map_mul, map_mul, mul_inv_rev]
      calc
        _ = f₁ x * ((f₁ y * (f₂ y)⁻¹) * (f₂ x)⁻¹) := by group
        _ = f₁ x * ((f₂ x)⁻¹ * (f₁ y * (f₂ y)⁻¹)) := by rw [hy]
        _ = _ := by group }
  have hker : (S : Subgroup D) ≤ d.ker := by
    intro x hx
    apply Subtype.ext
    change f₁ x * (f₂ x)⁻¹ = 1
    rw [hs x hx, mul_inv_cancel]
  obtain ⟨n, hn⟩ := (hp.to_subgroup d.range).exists_card_eq
  have hi : d.ker.index = p ^ n := (index_ker d).trans hn
  have hn0 : n = 0 := by
    by_contra hn0
    apply S.not_dvd_index
    apply dvd_trans _ (index_dvd_of_le hker)
    rw [hi]
    exact dvd_pow_self p hn0
  have ht : d.ker = ⊤ := index_eq_one.mp (by simpa [hn0] using hi)
  ext x
  have hx : x ∈ d.ker := ht ▸ mem_top x
  exact mul_inv_eq_one.mp (congrArg Subtype.val hx)
end MonoidHom
