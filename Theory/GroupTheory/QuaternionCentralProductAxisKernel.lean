module

public import Theory.GroupTheory.CyclicFourSubgroupAction
public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The axis-action kernel of a quaternion central product

For an extraspecial group of order thirty-two presented as a central product
of two quaternion groups, the action on cyclic subgroups of order four has the
same kernel as the action on the Frattini quotient.

Every order-four element has a square generating the order-two center, which
is the Frattini subgroup. Thus a trivial quotient action preserves each cyclic
subgroup of order four. Conversely, preserving such a subgroup sends its
generator to an odd power and hence fixes its Frattini coset. The standard
two generators of each quaternion factor then give triviality on the entire
quotient. In fact this argument only needs extraspeciality and generation by
the quaternion factors; the full central-product hypotheses are retained in
the public interface.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.390.
-/

namespace Subgroup
variable {H : Type*} [Group H] [Finite H] [IsExtraspecial 2 H]

private theorem center_le_axis (x : H) (hx : orderOf x = 4) :
    center H ≤ zpowers x := by
  have heq : zpowers (x ^ 2) = center H := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr (IsExtraspecial.square_mem_center x))
    rw [Nat.card_zpowers, orderOf_pow, hx, IsExtraspecial.center_order_p 2 H]
    decide
  rw [← heq]
  exact zpowers_le.mpr ((zpowers x).pow_mem (mem_zpowers x) 2)

private theorem axis_fixed_quotient (a : MulAut H) (x : H) (hx : orderOf x = 4)
    (ha : (zpowers x).map a.toMonoidHom = zpowers x) :
    QuotientGroup.mk' (frattini H) (a x) = QuotientGroup.mk' (frattini H) x := by
  classical
  have hamem : a x ∈ zpowers x := ha ▸ mem_map_of_mem a.toMonoidHom (mem_zpowers x)
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp
    ((isOfFinOrder_of_finite x).mem_zpowers_iff_mem_range_orderOf.mp hamem)
  have hn4 : n < 4 := by simpa [hx] using Finset.mem_range.mp hn
  have hao : orderOf (a x) = 4 := (a.orderOf_eq x).trans hx
  have hsq : x ^ 2 ∈ frattini H := by
    rw [IsExtraspecial.frattini_eq_center_two]
    exact IsExtraspecial.square_mem_center x
  let q := QuotientGroup.mk' (frattini H)
  have hq : q x ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hsq
  interval_cases n
  · simp only [pow_zero] at he
    rw [← he, orderOf_one] at hao
    norm_num at hao
  · simpa only [pow_one] using congrArg q he.symm
  · rw [← he, orderOf_pow, hx] at hao
    norm_num at hao
  · change q (a x) = q x
    rw [← he, map_pow, pow_succ, hq, one_mul]

omit [Finite H] [IsExtraspecial 2 H] in
private theorem quaternion_le_of_order_four (B K : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hK : ∀ x : H, orderOf x = 4 → x ∈ K) : B ≤ K := by
  obtain ⟨e⟩ := hB
  let f : QuaternionGroup 2 →* H := B.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := B.subtype_injective.comp e.symm.injective
  have ha : f (QuaternionGroup.a 1) ∈ K := hK _ (by
    rw [orderOf_injective f hf, QuaternionGroup.orderOf_a_one])
  have hb : f (QuaternionGroup.xa 0) ∈ K := hK _ (by
    rw [orderOf_injective f hf, QuaternionGroup.orderOf_xa])
  intro x hx
  have heq : f (e ⟨x, hx⟩) = x := by simp [f]
  rw [← heq]
  cases e ⟨x, hx⟩ with
  | a n =>
    have hn : (QuaternionGroup.a n : QuaternionGroup 2) = QuaternionGroup.a 1 ^ n.val := by simp
    rw [hn, map_pow]
    exact K.pow_mem ha _
  | xa n =>
    have hn : (QuaternionGroup.xa n : QuaternionGroup 2) =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ n.val := by simp
    rw [hn, map_mul, map_pow]
    exact K.mul_mem hb (K.pow_mem ha _)

set_option linter.unusedVariables false in
/-- For the quaternion central product of order thirty-two, the Frattini
quotient action and the intrinsic cyclic-four action have the same kernel. -/
public theorem quaternion_central_product_axis_kernel
    (hcard : Nat.card H = 32) (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hjoin : B ⊔ C = ⊤) :
    (quotientAut (frattini H)).ker = (cyclicFourAction (G := H)).ker := by
  ext a
  change quotientAut (frattini H) a = 1 ↔ cyclicFourAction a = 1
  rw [cyclicFourAction_eq_one_iff]
  constructor
  · intro ha x hx
    have he := DFunLike.congr_fun ha (QuotientGroup.mk' (frattini H) x)
    rw [quotientAut_apply_mk] at he
    have hd : x⁻¹ * a x ∈ center H := by
      rw [← IsExtraspecial.frattini_eq_center_two]
      exact QuotientGroup.eq.mp he.symm
    have hamem : a x ∈ zpowers x := by
      have hm := (zpowers x).mul_mem (mem_zpowers x) (center_le_axis x hx hd)
      simpa only [mul_inv_cancel_left] using hm
    rw [MonoidHom.map_zpowers]
    apply eq_of_le_of_card_ge (zpowers_le.mpr hamem)
    rw [Nat.card_zpowers, Nat.card_zpowers, a.orderOf_eq]
  · intro ha
    let q := QuotientGroup.mk' (frattini H)
    let K := (q.comp a.toMonoidHom).eqLocus q
    have hK : ∀ x : H, orderOf x = 4 → x ∈ K := by
      intro x hx
      exact axis_fixed_quotient a x hx (ha x hx)
    have htop : (⊤ : Subgroup H) ≤ K := by
      rw [← hjoin]
      exact sup_le (quaternion_le_of_order_four B K hB hK)
        (quaternion_le_of_order_four C K hC hK)
    apply MulEquiv.ext
    intro y
    induction y using Quotient.inductionOn with
    | h x =>
      change quotientAut (frattini H) a (q x) = q x
      rw [quotientAut_apply_mk]
      exact htop (mem_top x)

end Subgroup
