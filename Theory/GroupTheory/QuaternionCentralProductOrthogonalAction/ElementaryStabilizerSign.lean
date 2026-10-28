module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularPlaneSign
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoElementaryAlternative

/-!
# The factor sign of an elementary-eight stabilizer

An elementary subgroup of order eight contains the center of the quaternion
central product. Its central quotient is therefore a totally singular plane.
The explicit square coordinates carry any stabilizing automorphism to a wreath
isometry preserving that plane, whose product of factor signs is one.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

theorem squareCoordinates_quotientAut (a : MulAut Q) (v : Q ⧸ center Q) :
    d.squareCoordinates (Additive.ofMul (quotientAut (center Q) a v)) =
      (BinaryFourPlus.wreathToIsometry (d.quotientWreathAction a)).val
        (d.squareCoordinates (Additive.ofMul v)) := by
  have hc (i : BinaryFourPlus.C2) :
      BinaryFourPlus.coordinate
          (d.squareCoordinates (Additive.ofMul (quotientAut (center Q) a v))) i =
        BinaryFourPlus.coordinate
          ((BinaryFourPlus.wreathToIsometry (d.quotientWreathAction a)).val
            (d.squareCoordinates (Additive.ofMul v))) i := by
    rw [BinaryFourPlus.wreathToIsometry_coordinate]
    exact d.quotientWreathAction_apply a v i
  apply Prod.ext
  · simpa [BinaryFourPlus.coordinate] using hc 1
  · simpa only [BinaryFourPlus.coordinate,if_neg BinaryFourPlus.swapIndex_ne_one] using
      hc BinaryFourPlus.swapIndex

theorem quotientWreathAction_factorSign_one_of_elementary_eight
    (E : Subgroup Q) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (a : MulAut Q) (ha : ∀x∈E,a x∈E) :
    BinaryFourPlus.factorSign (d.quotientWreathAction a) = 1 := by
  let : IsExtraspecial 2 Q := d.extraspecial
  have hz : center Q ≤ E :=
    (IsExtraspecial.elementary_eight_normal_and_center_le_of_card_thirty_two d.card E hE).2
  let π := QuotientGroup.mk' (center Q)
  let H := E.map π
  have hindex : H.index = E.index := E.index_map_eq
    (QuotientGroup.mk'_surjective (center Q)) (by rw [QuotientGroup.ker_mk'];exact hz)
  have hEindex : E.index=4 := by
    have hh := E.card_mul_index
    rw [hE,d.card] at hh
    omega
  have hHcard : Nat.card H=4 := by
    have hh := H.card_mul_index
    rw [hindex,hEindex,d.quotient_card] at hh
    omega
  let W : Submodule (ZMod 2) d.SquareSpace := {
    carrier := {v | v.toMul∈H}
    zero_mem' := H.one_mem
    add_mem' := fun hx hy=>H.mul_mem hx hy
    smul_mem' := by
      intro r v hv
      have hb : ∀r:ZMod 2,r=0 ∨ r=1 := by decide
      rcases hb r with rfl|rfl
      · rw [zero_smul];exact H.one_mem
      · simpa only [one_smul] using hv }
  have hcW : Nat.card W=4 := by
    let e : W ≃ H := {
      toFun := fun v=>⟨v.val.toMul,v.property⟩
      invFun := fun v=>⟨Additive.ofMul v.val,v.property⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
    exact (Nat.card_congr e).trans hHcard
  have hdW : Module.finrank (ZMod 2) W=2 := by
    have hc := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=W)
    rw [hcW,Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2≤2) hc.symm
  have hsW : ∀v∈W,d.quadraticForm v=0 := by
    intro v hv
    obtain ⟨x,hx,he⟩ := hv
    have hs : x^2=1 := elemPow_eq_one_of_isElementaryAbelian x hx
    have hev : v=Additive.ofMul (π x) := congrArg Additive.ofMul he.symm
    rw [hev,d.quadraticForm_apply,d.binarySquare_mk]
    have hsq : (⟨x^2,d.square_mem_center x⟩:center Q)=1 := Subtype.ext hs
    rw [hsq,map_one]
    rfl
  let B := W.map d.squareCoordinates.toLinearMap
  have hdB : Module.finrank (ZMod 2) B=2 := by
    rw [LinearEquiv.finrank_map_eq]
    exact hdW
  have hsB : ∀v∈B,BinaryFourPlus.q v=0 := by
    rintro v ⟨w,hw,rfl⟩
    have he := d.squareFormIsometry.map_app' w
    change BinaryFourPlus.q (d.squareFormIsometry w)=d.quadraticForm w at he
    rw [squareFormIsometry_apply] at he
    change BinaryFourPlus.q (d.squareCoordinates w)=0
    exact he.trans (hsW w hw)
  apply BinaryFourPlus.invariant_singular_plane_factorSign_one B (by rw [hdB]) hsB
  rintro v ⟨w,hw,rfl⟩
  obtain ⟨x,hx,hxw⟩ := hw
  have hnew : Additive.ofMul (quotientAut (center Q) a w.toMul)∈W := by
    change quotientAut (center Q) a w.toMul∈H
    rw [←hxw,quotientAut_apply_mk]
    exact mem_map_of_mem π (ha x hx)
  exact ⟨_,hnew,d.squareCoordinates_quotientAut a w.toMul⟩
end Subgroup.QuaternionCentralProductData
