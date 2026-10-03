module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Intersecting two normal-subgroup covers

Let `A`, `B`, and `C` be normal subgroups with `AB = AC = G`. If the two
intersections `A ∩ B` and `A ∩ C` generate `A`, then `A(B ∩ C) = G`.
No finiteness is needed.

Substituting the intersection decomposition of `A` into `AB = G` gives
`B(A ∩ C) = G`. Write an element `c` of `C` as `bd`, with `b ∈ B` and
`d ∈ A ∩ C`. Then `b = cd⁻¹` also lies in `C`, so
`C ≤ A(B ∩ C)`. The other cover `AC = G` finishes the argument.

This elementary subgroup calculation supplies the normal-cover intersection
step in Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.3)(1).
-/

namespace Subgroup

/-- Two normal covers remain a cover after intersecting their second factors
when the corresponding intersections generate the common first factor. -/
public theorem sup_inf_eq_top_of_normal_covers
    {G : Type*} [Group G] (A B C : Subgroup G)
    [A.Normal] [B.Normal] [C.Normal]
    (hAB : A ⊔ B = ⊤) (hAC : A ⊔ C = ⊤)
    (hA : (A ⊓ B) ⊔ (A ⊓ C) = A) : A ⊔ (B ⊓ C) = ⊤ := by
  have hBC : B ⊔ (A ⊓ C) = ⊤ := by
    apply top_unique
    apply hAB.symm.le.trans
    exact sup_le
      (hA.symm.le.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right))
      le_sup_left
  have hC : C ≤ A ⊔ (B ⊓ C) := by
    intro c hc
    have hc' : c ∈ B ⊔ (A ⊓ C) := by rw [hBC]; trivial
    obtain ⟨b, hb, d, hd, hbd⟩ := mem_sup_of_normal_right.mp hc'
    have hbC : b ∈ C := by
      have hmem := C.mul_mem hc (C.inv_mem hd.2)
      rw [← hbd] at hmem
      simpa only [mul_inv_cancel_right] using hmem
    rw [← hbd]
    exact (A ⊔ (B ⊓ C)).mul_mem
      ((show B ⊓ C ≤ A ⊔ (B ⊓ C) from le_sup_right) ⟨hb, hbC⟩)
      ((show A ≤ A ⊔ (B ⊓ C) from le_sup_left) hd.1)
  apply top_unique
  rw [← hAC]
  exact sup_le le_sup_left hC

end Subgroup
