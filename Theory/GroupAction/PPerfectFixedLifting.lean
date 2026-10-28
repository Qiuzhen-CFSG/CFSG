module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.PPerfectHom

/-!
# Lifting fixation of p-perfect subgroups

For an equivariant homomorphism with central p-group kernel, fixation of
the image of a p-perfect subgroup implies pointwise fixation upstairs.
The displacement x ↦ a(x)x⁻¹ is a homomorphism into the central kernel,
and p-perfectness makes it trivial. No invariance of the subgroup under
the automorphism, or surjectivity of the homomorphism, is assumed.

Source application: the embedded residual comparison in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 16.5.5–6, printed p.1197.
-/

public section
namespace MulAut
open Subgroup

variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

/-- Central p-valued displacement vanishes on a p-perfect subgroup. -/
theorem fixes_of_fixes_image_of_central_pgroup_ker
    (a : MulAut G) (b : MulAut H) (f : G →* H)
    (hc : f.ker ≤ center G) (hp : IsPGroup p f.ker)
    (heq : ∀ x, f (a x) = b (f x))
    (X : Subgroup G) (hX : IsPPerfect p X)
    (hfix : X.map f ≤ b.fixedSubgroup) : X ≤ a.fixedSubgroup := by
  have hdmem (x : X) : a x * (x : G)⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq]
    rw [(mem_fixedSubgroup _ _).mp (hfix (mem_map_of_mem f x.property)), mul_inv_cancel]
  let d : X →* f.ker := {
    toFun x := ⟨a x * (x : G)⁻¹, hdmem x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change a ((x : G) * y) * ((x : G) * y)⁻¹ =
        (a x * (x : G)⁻¹) * (a y * (y : G)⁻¹)
      have hy := mem_center_iff.mp (hc (hdmem y)) (x : G)⁻¹
      rw [map_mul, mul_inv_rev]
      calc
        _ = a x * ((a y * (y : G)⁻¹) * (x : G)⁻¹) := by group
        _ = a x * ((x : G)⁻¹ * (a y * (y : G)⁻¹)) := by rw [hy]
        _ = _ := by group }
  have hd := hX.hom_eq_one_of_isPGroup hp d
  intro x hx
  have hx' := congrArg (fun k : X →* f.ker => (k ⟨x, hx⟩ : G)) hd
  exact (mem_fixedSubgroup _ _).mpr (mul_inv_eq_one.mp hx')

/-- Fixation is equivalent before and after passage through a central p-kernel. -/
theorem fixes_image_iff_of_central_pgroup_ker
    (a : MulAut G) (b : MulAut H) (f : G →* H)
    (hc : f.ker ≤ center G) (hp : IsPGroup p f.ker)
    (heq : ∀ x, f (a x) = b (f x))
    (X : Subgroup G) (hX : IsPPerfect p X) :
    X.map f ≤ b.fixedSubgroup ↔ X ≤ a.fixedSubgroup := by
  refine ⟨fixes_of_fixes_image_of_central_pgroup_ker a b f hc hp heq X hX, ?_⟩
  rintro h _ ⟨x, hx, rfl⟩
  apply (mem_fixedSubgroup _ _).mpr
  rw [← heq, (mem_fixedSubgroup _ _).mp (h hx)]

end MulAut
