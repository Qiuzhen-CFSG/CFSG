module
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionTypes
public import Theory.GroupTheory.QuaternionCentralProductC2Action
public import Theory.Representation.InvertedThreeCentralizer

/-!
# The fixed plane of a quaternion involution

An involution of a quaternion central product with four fixed vectors on the
square quotient either preserves the two factors and has type c₂, or swaps
them and has type a₂. In the preserving case an invariant quaternion axis
supplies a nonsingular fixed vector. The intrinsic c₂ criterion then proves
that both factor restrictions are outer. We also identify the square-quotient
c₂ predicate with the moved-dimension predicate used by the rank theorem.

The fixed order four follows from the norm identity for an inverted cubic on
the literal square space. The marked cubic and its full commutator hypothesis
are connected to that identity in `ActionDichotomy.MarkedCubic`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Definition E.2.6,
printed p.218, and the quaternion-action step of Lemma 14.4.4, printed p.1007.
-/

open Subgroup
open scoped IsMulCommutative
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

private def fixedLinearEquiv (a : MulAut Q) :
    d.fixedSquareQuotient a ≃ LinearMap.ker ((d.quotientLinearAction a).toLinearMap - 1) where
  toFun x := ⟨Additive.ofMul x.val, by
    change d.quotientLinearAction a (Additive.ofMul x.val) - Additive.ofMul x.val = 0
    rw [d.quotientLinearAction_apply]
    exact sub_eq_zero.mpr (congrArg Additive.ofMul x.property)⟩
  invFun x := ⟨x.val.toMul, by
    have hx : d.quotientLinearAction a x.val - x.val = 0 := x.property
    rw [show x.val = Additive.ofMul x.val.toMul from rfl,
      d.quotientLinearAction_apply] at hx
    exact congrArg Additive.toMul (sub_eq_zero.mp hx)⟩
  left_inv _ := rfl
  right_inv _ := rfl

public theorem isC2Action_iff_isC2 (a : MulAut Q) : d.IsC2Action a ↔ d.IsC2 a := by
  rw [d.isC2Action_iff_source]
  constructor
  · rintro ⟨ha, hc, v, hv⟩
    have hkcard : Nat.card (LinearMap.ker ((d.quotientLinearAction a).toLinearMap - 1)) = 4 :=
      (Nat.card_congr (fixedLinearEquiv d a)).symm.trans hc
    have hkdim : Module.finrank (ZMod 2)
        (LinearMap.ker ((d.quotientLinearAction a).toLinearMap - 1)) = 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hkcard
      have hp : (2 : ℕ) ^ Module.finrank (ZMod 2)
          (LinearMap.ker ((d.quotientLinearAction a).toLinearMap - 1)) = 2 ^ 2 := hkcard
      exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hp
    refine ⟨ha, ?_, Additive.ofMul v, ?_⟩
    · have hr := LinearMap.finrank_range_add_finrank_ker
        ((d.quotientLinearAction a).toLinearMap - 1)
      rw [hkdim, d.quotient_finrank] at hr
      change Module.finrank (ZMod 2)
        (LinearMap.range ((d.quotientLinearAction a).toLinearMap - 1)) = 2
      omega
    · simpa only [d.quotientLinearAction_apply] using hv
  · intro h
    refine ⟨h.involutive, IsC2.fixed_quotient_card d h, ?_⟩
    obtain ⟨v, hv⟩ := h.nonorthogonal
    refine ⟨v.toMul, ?_⟩
    change d.quadraticForm.polarBilin v
      (Additive.ofMul (quotientAut (center Q) a v.toMul)) ≠ 0
    rw [← d.quotientLinearAction_apply]
    exact hv

private theorem factor_square_one_mem_center
    (B C : Subgroup Q) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup Q) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (hZ : B ⊓ C = center Q) (b : B) (hb : (b : Q)^2=1) : (b : Q) ∈ center Q := by
  have hm : b ∈ center B := by
    let e := hB.some
    have ht : ∀ x : QuaternionGroup 2, x^2=1 → ∀ y, y*x=x*y := by decide
    have hb' : (e b)^2=1 := by rw [← map_pow, show b^2=1 from Subtype.ext hb, map_one]
    exact mem_center_iff.mpr fun y => e.injective (by simpa only [map_mul] using ht (e b) hb' (e y))
  rw [← hZ, intersection_eq_factor_center B C hB hinter hcomm]
  exact mem_map_of_mem B.subtype hm

private theorem nonsingular_fixed_of_preserves (a : MulAut Q) (ha : a^2=1)
    (hB : d.left.map a.toMonoidHom = d.left) :
    ∃ v ∈ d.fixedSquareQuotient a, d.square v ≠ 1 := by
  let _ := d.quotient_elementary
  let π := QuotientGroup.mk' (center Q)
  let β := quotientAut (center Q) a
  have hβ2 (v : Q ⧸ center Q) : β (β v) = v := by
    have hh : β^2=1 := by dsimp [β]; rw [← map_pow, ha, map_one]
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hh v
  have hi (v : Q ⧸ center Q) : v⁻¹ = v := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      d.quotient_elementary.exponent_dvd_p v
  let b : d.left := d.left_model.some.symm (QuaternionGroup.a 1)
  have hb : (b : Q)^2 ≠ 1 := by
    intro h
    have h' := congrArg d.left_model.some (show b^2=1 from Subtype.ext h)
    simp only [map_pow, map_one, b, MulEquiv.apply_symm_apply] at h'
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2)^2 ≠ 1) h'
  by_cases hf : β (π b) = π b
  · refine ⟨π b, hf, ?_⟩
    intro hs
    apply hb
    have h := congrArg Subtype.val hs
    simpa only [π, d.square_mk, coe_one] using h
  · let c : Q := (b : Q)⁻¹ * a b
    have hcB : c ∈ d.left := d.left.mul_mem (d.left.inv_mem b.property)
      (hB.le (mem_map_of_mem a.toMonoidHom b.property))
    have he : π c = (π b)⁻¹ * β (π b) := by
      rw [quotientAut_apply_mk]
      exact map_mul π _ _ |>.trans (congrArg (· * π (a b)) (map_inv π _))
    have hc1 : π c ≠ 1 := by
      rw [he, ne_eq, inv_mul_eq_one]
      exact fun h => hf h.symm
    refine ⟨π c, ?_, ?_⟩
    · change β (π c) = π c
      rw [he, map_mul, map_inv, hβ2, hi, hi, mul_comm]
    · intro hs
      have hsq : c^2=1 := by
        have h := congrArg Subtype.val hs
        simpa only [π, d.square_mk, coe_one] using h
      exact hc1 ((QuotientGroup.eq_one_iff _).mpr
        (factor_square_one_mem_center d.left d.right d.left_model d.intersection_card
          d.commute d.center_eq.symm ⟨c,hcB⟩ hsq))

public theorem action_dichotomy_of_fixed_four (a : MulAut Q) (ha : a^2=1)
    (hc : Nat.card (d.fixedSquareQuotient a) = 4) :
    (d.IsC2Action a ∧ d.BothOuter a) ∨
      (d.left.map a.toMonoidHom = d.right ∧ d.IsA2Action a) := by
  have him := quaternion_subgroup_eq_factor d.left d.right
    (d.left.map a.toMonoidHom) d.left_model d.right_model d.intersection_card d.commute
    ⟨(a.subgroupMap d.left).symm.trans d.left_model.some⟩ (by rw [d.span]; exact le_top)
  rcases him with hpres | hswap
  · have h : d.IsC2Action a := ⟨by rw [← map_pow, ha, map_one], hc,
        nonsingular_fixed_of_preserves d a ha hpres⟩
    exact Or.inl ⟨h, IsC2.bothOuter d ((d.isC2Action_iff_isC2 a).mp h)⟩
  · exact Or.inr ⟨hswap, d.isA2Action_of_swap a ha hswap⟩

/-- Rank-nullity for a cubic inverted by the involution, on the actual square space. -/
public theorem fixed_card_of_inverted_cubic (a : MulAut Q) (ha : a^2=1)
    (t : Module.End (ZMod 2) d.SquareSpace) (ht : t^2+t+1=0)
    (hinv : (d.quotientLinearAction a).toLinearMap * t =
      t^2 * (d.quotientLinearAction a).toLinearMap) :
    Nat.card (d.fixedSquareQuotient a) = 4 := by
  rw [Nat.card_congr (fixedLinearEquiv d a)]
  apply Representation.invertedThree_cardSixteen_fixed_card_four t
    (d.quotientLinearAction a).toLinearMap ht ?_ hinv
    ((Nat.card_congr Additive.toMul).trans d.quotient_card)
  have h := congrArg LinearEquiv.toLinearMap
    (show (d.quotientLinearAction a)^2=1 by rw [← map_pow, ha, map_one])
  exact h

end Subgroup.QuaternionCentralProductData
