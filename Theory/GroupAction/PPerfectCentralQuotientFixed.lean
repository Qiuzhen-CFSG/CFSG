module

public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Fixation through a central p-group kernel

An automorphism fixing the image of a p-perfect subgroup under a homomorphism
with central p-group kernel fixes that subgroup pointwise. The displacement
map is a homomorphism into the kernel, so p-perfectness kills it. No invariance
of the subgroup under the automorphism is assumed.

This supports the full-cover action comparison in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Notation 16.5.5, printed p.1197.
-/

public section

open Subgroup

namespace MulAut
variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

/-- Fixation of a p-perfect subgroup can be tested after a central p-group
quotient, without assuming that the automorphism preserves the subgroup. -/
theorem fixed_of_fixed_mod_central_p_kernel (f : G →* H) (a : MulAut G)
    (A : Subgroup G) (hA : IsPPerfect p A)
    (hp : IsPGroup p f.ker) (hc : f.ker ≤ center G)
    (ha : ∀ x ∈ A, f (a x) = f x) : ∀ x ∈ A, a x = x := by
  have hd (x : A) : x.val⁻¹ * a x.val ∈ f.ker := by
    change f (x.val⁻¹ * a x.val) = 1
    rw [map_mul, map_inv, ha x x.property, inv_mul_cancel]
  let δ : A →* f.ker := {
    toFun x := ⟨x.val⁻¹ * a x.val, hd x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change ((x : G) * y)⁻¹ * a ((x : G) * y) =
        (x.val⁻¹ * a x.val) * (y.val⁻¹ * a y.val)
      rw [mul_inv_rev, map_mul]
      have hxy := mem_center_iff.mp (hc (hd x)) y.val⁻¹
      calc
        y.val⁻¹ * x.val⁻¹ * (a x.val * a y.val) =
            (y.val⁻¹ * (x.val⁻¹ * a x.val)) * a y.val := by group
        _ = ((x.val⁻¹ * a x.val) * y.val⁻¹) * a y.val := by rw [hxy]
        _ = _ := by group }
  have hδ := hA.hom_eq_one_of_isPGroup hp δ
  intro x hx
  have he := congrArg (fun b : A →* f.ker => ((b ⟨x, hx⟩ : f.ker) : G)) hδ
  change x⁻¹ * a x = 1 at he
  exact (inv_mul_eq_one.mp he).symm
end MulAut
