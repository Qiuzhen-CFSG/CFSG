module
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.ElementaryAbelian.Basic

/-!
# Elementary abelian quotients of relative conjugate spans

An abelian quotient of the span of conjugates of an elementary abelian
p-subgroup has exponent dividing p. Induction on the original conjugate
closure proves the power identity before passing to the quotient. Neither
ambient normality nor commutativity of the numerator is required.

Source application: Aschbacher--Smith 13.8.29(4), printed p.964.
-/

public section
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

/-- An abelian quotient of a relative elementary conjugate span is elementary. -/
theorem conjugateSpan_quotient_elementary (p : ℕ) (A H Z : Subgroup G)
    [IsElementaryAbelian p A]
    [(Z.subgroupOf (conjugateSpanBy A H)).Normal]
    [hab : IsMulCommutative ((conjugateSpanBy A H) ⧸ Z.subgroupOf (conjugateSpanBy A H))] :
    IsElementaryAbelian p ((conjugateSpanBy A H) ⧸ Z.subgroupOf (conjugateSpanBy A H)) := by
  let S := conjugateSpanBy A H
  let q := QuotientGroup.mk' (Z.subgroupOf S)
  have hp (x : G) (hx : x ∈ S) : q ⟨x,hx⟩ ^ p = 1 := by
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h,_,a,ha,rfl⟩ := hx
      have he : (⟨h*a*h⁻¹,subset_closure ⟨h,‹h ∈ H›,a,ha,rfl⟩⟩ : S) ^ p = 1 := by
        apply Subtype.ext
        change (h*a*h⁻¹)^p = 1
        rw [conj_pow,elemPow_eq_one_of_isElementaryAbelian a ha,mul_one,mul_inv_cancel]
      rw [←map_pow,he,map_one]
    | one => change q 1 ^ p = 1; rw [map_one,one_pow]
    | mul x y hx hy ihx ihy =>
      change (q ⟨x,hx⟩ * q ⟨y,hy⟩)^p = 1
      rw [mul_pow,ihx,ihy,one_mul]
    | inv x hx ih =>
      change (q ⟨x,hx⟩)⁻¹ ^ p = 1
      rw [inv_pow,ih,inv_one]
  refine {
    toIsMulCommutative := hab
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  induction x using QuotientGroup.induction_on with
  | H x => exact hp x x.property

end Subgroup

