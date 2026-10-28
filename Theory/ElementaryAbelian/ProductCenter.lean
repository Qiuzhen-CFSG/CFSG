module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Center of a product of elementary abelian two-groups

If elementary abelian two-subgroups `C` and `D` satisfy that `C` normalizes
`D`, then the center of their join is elementary abelian. The center is
commutative; to check its exponent, write a central element as `d * c`.
Its commutation with `c` implies that `d` and `c` commute, so its square is
the product of their squares and hence is one.

This normalized-product calculation supplies the elementary center module
used in Stellmacher (9.1), relation (3); see
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

public theorem isElementaryAbelian_center_sup_of_normalizes
    {G : Type*} [Group G] (C D : Subgroup G)
    [IsElementaryAbelian 2 C] [IsElementaryAbelian 2 D]
    (hn : C ≤ Subgroup.normalizer (D : Set G)) :
    IsElementaryAbelian 2 (Subgroup.center ↥(C ⊔ D)) := by
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro z
  apply Subtype.ext
  apply Subtype.ext
  have hzprod : ((z : ↥(C ⊔ D)) : G) ∈ (D : Set G) * (C : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left D C hn, sup_comm]
    exact (z : ↥(C ⊔ D)).property
  obtain ⟨d, hd, c, hc, hdc⟩ := hzprod
  have hzcomm : c * ((z : ↥(C ⊔ D)) : G) = ((z : ↥(C ⊔ D)) : G) * c := by
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property
      (⟨c, (show C ≤ C ⊔ D from le_sup_left) hc⟩ : ↥(C ⊔ D)))
  have hcomm : Commute d c := by
    change d * c = c * d
    rw [← hdc, ← mul_assoc] at hzcomm
    exact (mul_right_cancel hzcomm).symm
  change ((z : ↥(C ⊔ D)) : G) ^ 2 = 1
  rw [← hdc, hcomm.mul_pow,
    elemPow_eq_one_of_isElementaryAbelian d hd,
    elemPow_eq_one_of_isElementaryAbelian c hc, one_mul]
