module
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Inverting an order-four lift using a quotient displacement

For an involutory automorphism a, the element k*a(k)⁻¹ is inverted by a.
If its image in the central quotient is a non-two-central involution,
I.2.2's order-four lifting input forces this particular representative to
have order four. Perfectness makes quotient actions faithful, preserving
both the order and outerness of an automorphism.

This proves the deduction from observation (iii) to the inversion clause
of Aschbacher–Smith I.2.2(5b), printed p.411 / PDF p.422 (combined
1 March 2004 manuscript). The required quotient displacement and
non-two-central lifting are independent, explicit premises. No exceptional
group's displacement calculation or covering statement is assumed proved.
-/

@[expose] public section
namespace Theory.GroupTheory.DoubleCoverCentralizer
open Subgroup
variable {K S : Type*} [Group K] [Group S]

/-- A non-two-central quotient involution obtained as x*a(x)⁻¹. -/
def HasNonTwoCentralDisplacement (a : MulAut S) : Prop :=
  ∃ x : S, orderOf (x * (a x)⁻¹) = 2 ∧ ¬ TwoCentral (x * (a x)⁻¹)

/-- Lift a quotient displacement, retaining its mark and the inverting automorphism. -/
theorem inverts_four_of_quotient_displacement [Finite K]
    (e : K ⧸ center K ≃* S) (hZ : Nat.card (center K) = 2)
    (hlift : NonTwoCentralInvolutionLifting K)
    (a : MulAut K) (ha : orderOf a = 2)
    (hd : HasNonTwoCentralDisplacement (MulAut.centralQuotientAction e a)) :
    ∃ y : K, orderOf y = 4 ∧ a y = y⁻¹ ∧
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
  refine ⟨y, order_four_of_marked_coset hZ hlift y hy2 hym, ?_, hym⟩
  have haa : a (a k) = k := by
    have hp : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
    have hh := DFunLike.congr_fun hp k
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  simp only [y, map_mul, map_inv, haa, mul_inv_rev, inv_inv]

/-- The two independent model inputs imply the source outer-inversion clause. -/
theorem outer_inverts_four_of_model_displacements [Finite K] [Group.IsPerfect K]
    (e : K ⧸ center K ≃* S) (hZ : Nat.card (center K) = 2)
    (hlift : NonTwoCentralInvolutionLifting K)
    (hmodel : ∀ b : MulAut S, orderOf b = 2 → (¬ ∃ s : S, b = MulAut.conj s) →
      HasNonTwoCentralDisplacement b)
    (a : MulAut K) (ha : orderOf a = 2) (hao : ¬ ∃ k : K, a = MulAut.conj k) :
    ∃ y : K, orderOf y = 4 ∧ a y = y⁻¹ ∧
      ¬ TwoCentral (QuotientGroup.mk' (center K) y) := by
  apply inverts_four_of_quotient_displacement e hZ hlift a ha
  apply hmodel
  · exact (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) a).trans ha
  · exact fun h => hao ((MulAut.centralQuotientAction_inner_iff e a).mp h)

end Theory.GroupTheory.DoubleCoverCentralizer
