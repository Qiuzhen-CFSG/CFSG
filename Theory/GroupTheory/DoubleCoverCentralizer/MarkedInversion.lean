module

public import Theory.GroupTheory.DoubleCoverCentralizer.InvertedDisplacement

/-!
# An inverted lift with its original quotient involution retained

Lift the actual displacement witness and use `k * a(k)⁻¹`. Its image remains
an involution in the specified central quotient. This marking, together with
the order-four conclusion, identifies its square in a central double cover.

Source: Aschbacher–Smith I.2.2, observation (iii), printed p.411, and the
J₂-cover exclusion in 2.5.19, printed p.562.
-/

public section
namespace Theory.GroupTheory.DoubleCoverCentralizer
open Subgroup
variable {K S : Type*} [Group K] [Group S]

/-- The displacement construction retains the order of its original quotient image. -/
theorem inverts_four_with_involution_image [Finite K]
    (e : K ⧸ center K ≃* S) (hZ : Nat.card (center K) = 2)
    (hlift : NonTwoCentralInvolutionLifting K)
    (a : MulAut K) (ha : orderOf a = 2)
    (hd : HasNonTwoCentralDisplacement (MulAut.centralQuotientAction e a)) :
    ∃ y : K, orderOf y = 4 ∧ a y = y⁻¹ ∧
      orderOf (QuotientGroup.mk' (center K) y) = 2 ∧
      ¬ TwoCentral (QuotientGroup.mk' (center K) y) := by
  obtain ⟨x, hx, hn⟩ := hd
  obtain ⟨k, hk⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center K))) x
  change e (QuotientGroup.mk' (center K) k) = x at hk
  let y := k * (a k)⁻¹
  have hy : e (QuotientGroup.mk' (center K) y) =
      x * (MulAut.centralQuotientAction e a x)⁻¹ := by
    change e (QuotientGroup.mk' (center K) (k * (a k)⁻¹)) = _
    rw [map_mul, map_inv, map_mul, map_inv,
      ← MulAut.centralQuotientAction_apply, hk]
  have hy2 : orderOf (QuotientGroup.mk' (center K) y) = 2 := by
    rw [← e.orderOf_eq, hy, hx]
  have hym : ¬ TwoCentral (QuotientGroup.mk' (center K) y) := by
    intro hh
    exact hn (hy ▸ hh.map e)
  refine ⟨y, order_four_of_marked_coset hZ hlift y hy2 hym, ?_, hy2, hym⟩
  have haa : a (a k) = k := by
    have hp : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
    have hh := DFunLike.congr_fun hp k
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  simp only [y, map_mul, map_inv, haa, mul_inv_rev, inv_inv]

end Theory.GroupTheory.DoubleCoverCentralizer
