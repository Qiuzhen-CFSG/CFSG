module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.ActorLifting
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.PlaneCentralizers
/-!
# Involutions outside the marked root group

An actor is diagonal or diagonal times graph–field. A diagonal actor with
square one is trivial, since the diagonal group has odd order. In the other
coset, the two root coordinates are interchanged. The commuting equations
then force any centralized root involution into the center.

This supplies the elementary-subgroup exhaustion in the Sylow subgroup of
the source group, without enumerating subgroup subsets.
Source: Aschbacher, *Sporadic Groups* (1994), 46.14(2), pp.257–258.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel
open Cubic Theory.GroupTheory.HyperbolicRecognition

private theorem diagonal_eq_one_of_square (s : actor) (hs : s ^ 2 = 1)
    (a : Fˣ × Fˣ) (ha : (s : MulAut Root) = diagonalHom a) : s = 1 := by
  have ha2 : a ^ 2 = 1 := by
    apply diagonalHom_injective
    rw [map_pow, ← ha]
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_one] using congrArg Subtype.val hs
  have hc : Nat.card (Fˣ × Fˣ) = 9 := by
    rw [Nat.card_prod, Nat.card_units, card_F]
  have ha9 : a ^ 9 = 1 := hc ▸ (pow_card_eq_one' (x := a))
  have ha1 : a = 1 := by
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha2) (orderOf_dvd_of_pow_eq_one ha9)
    have ho : orderOf a = 1 := Nat.eq_one_of_dvd_one hd
    exact orderOf_eq_one_iff.mp ho
  apply Subtype.ext
  rw [ha,ha1,map_one]
  rfl

/-- An involution outside the root has no noncentral root involution in its centralizer. -/
theorem involution_centralizes_root_involution (g : Model) (q : Root)
    (hg : g ^ 2 = 1) (hq : q ^ 2 = 1)
    (hc : g * SemidirectProduct.inl q = SemidirectProduct.inl q * g)
    (hn : q ∉ center Root) : g ∈ root := by
  obtain ⟨a,ha | ha⟩ := actor_normal_form g.right
  · apply (mem_root g).mpr
    apply diagonal_eq_one_of_square g.right _ a ha
    simpa only [pow_two,SemidirectProduct.mul_right,SemidirectProduct.one_right] using
      congrArg SemidirectProduct.right hg
  · have h := (commute_inl_iff g q).mp hc
    rw [ha] at h
    have hx := congrArg SylowModel.U.x h
    have hy := congrArg SylowModel.U.y h
    have hx' : (a.1 : F) * fieldFrobenius q.y = q.x := by
      change g.left.x + (a.1 : F) * fieldFrobenius q.y = q.x + g.left.x at hx
      exact add_left_cancel (hx.trans (add_comm _ _))
    have hy' : (a.2 : F) * fieldFrobenius q.x = q.y := by
      change g.left.y + (a.2 : F) * fieldFrobenius q.x = q.y + g.left.y at hy
      exact add_left_cancel (hy.trans (add_comm _ _))
    have hxy := (root_square_eq_one q).mp hq
    exfalso
    apply hn
    rw [SylowModel.mem_center_U]
    rcases mul_eq_zero.mp hxy with hx0 | hy0
    · exact ⟨hx0, by simpa [hx0] using hy'.symm⟩
    · exact ⟨by simpa [hy0] using hx'.symm,hy0⟩
end Matrix.PSL3Four.RootNormalizerModel
