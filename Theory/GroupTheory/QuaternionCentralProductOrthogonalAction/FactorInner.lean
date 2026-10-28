module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FactorCoordinates
public import Theory.GroupTheory.QuaternionCentralProductC2Rank
import all Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry.Coordinates

/-!
# Detecting outer restrictions on the marked quaternion factors

An inner action on one quaternion factor fixes its plane in Q/Z(Q).
The two marked generator vectors form a basis of that plane, so the
corresponding S₃ coordinate of the square-wreath action is the identity.
Consequently nontrivial coordinates on both preserved planes give outer
restrictions on both original factors.

The internal Coordinates import exposes the generator definition only
inside this descendant proof; its private coordinates do not occur in the
public interface. This is the factor-action bridge used by I.4.5's
ExtensionInvolution consumer, without changing the shared geometry API.
Source: Fong–Wong §2F, Nagoya Math. J.36 (1969), pp.153–154; the intrinsic
square-quotient convention is Aschbacher–Smith E.2.6 and 14.2.21.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

private theorem axis_eq_one_of_fixed_basis (a : MulAut Q) (i : BinaryFourPlus.C2)
    (hs : (d.quotientWreathAction a).right=1) (v : Fin 2 → d.SquareSpace)
    (hv : ∀j, BinaryFourPlus.coordinate (d.squareCoordinates (v j)) i = Pi.single j 1)
    (hfix : ∀j, quotientAut (center Q) a (v j).toMul = (v j).toMul) :
    (d.quotientWreathAction a).left i = 1 := by
  apply BinaryFourPlus.planeLinear_injective
  rw [BinaryFourPlus.planeLinear_one]
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin 2)).ext
  intro j
  have hh := d.quotientWreathAction_apply a (v j).toMul i
  rw [hfix,hs,inv_one,one_mul] at hh
  change BinaryFourPlus.coordinate (d.squareCoordinates (v j)) i =
    BinaryFourPlus.planeLinear ((d.quotientWreathAction a).left i)
      (BinaryFourPlus.coordinate (d.squareCoordinates (v j)) i) at hh
  rw [hv] at hh
  simpa using hh.symm

private theorem fixes_factor_of_inner (B : Subgroup Q) (e : B ≃* QuaternionGroup 2)
    (a : MulAut Q) (hb : ∃ b : B, ∀ x : B, a (x:Q) = (b:Q)*x*(b:Q)⁻¹) :
    ∀j, quotientAut (center Q) a (d.factorVector B e j).toMul = (d.factorVector B e j).toMul := by
  obtain ⟨b,hb⟩ := hb
  let _ := d.quotient_elementary
  intro j
  rw [factorVector]
  change quotientAut (center Q) a (QuotientGroup.mk' (center Q) (e.symm (qgen j) : Q)) =
    QuotientGroup.mk' (center Q) (e.symm (qgen j) : Q)
  rw [quotientAut_apply_mk,hb]
  simp only [map_mul,map_inv]
  rw [mul_comm _ (QuotientGroup.mk' (center Q) (e.symm _ : Q)),mul_inv_cancel_right]

theorem quotientWreathAction_left_one_of_inner (a : MulAut Q)
    (hs : (d.quotientWreathAction a).right=1)
    (hb : ∃ b : d.left, ∀ x : d.left, a (x:Q) = (b:Q)*x*(b:Q)⁻¹) :
    (d.quotientWreathAction a).left 1 = 1 := by
  apply axis_eq_one_of_fixed_basis d a 1 hs (d.factorVector d.left d.left_model.some)
  · intro j
    rw [d.squareCoordinates_factor_left]
    simp [BinaryFourPlus.coordinate]
  · exact fixes_factor_of_inner d d.left d.left_model.some a hb

theorem quotientWreathAction_right_one_of_inner (a : MulAut Q)
    (hs : (d.quotientWreathAction a).right=1)
    (hb : ∃ b : d.right, ∀ x : d.right, a (x:Q) = (b:Q)*x*(b:Q)⁻¹) :
    (d.quotientWreathAction a).left BinaryFourPlus.swapIndex = 1 := by
  apply axis_eq_one_of_fixed_basis d a BinaryFourPlus.swapIndex hs
    (d.factorVector d.right d.right_model.some)
  · intro j
    rw [d.squareCoordinates_factor_right]
    simp [BinaryFourPlus.coordinate,BinaryFourPlus.swapIndex_ne_one]
  · exact fixes_factor_of_inner d d.right d.right_model.some a hb

/-- Nontrivial permutations on both quotient planes detect both outer restrictions. -/
theorem bothOuter_of_nontrivial_axes (a : MulAut Q)
    (hs : (d.quotientWreathAction a).right=1)
    (hl : (d.quotientWreathAction a).left 1 ≠ 1)
    (hr : (d.quotientWreathAction a).left BinaryFourPlus.swapIndex ≠ 1) : d.BothOuter a := by
  have hL := (d.quotientWreathAction_right_eq_one_iff a).mp hs
  have hR : d.right.map a.toMonoidHom = d.right := by
    rcases (d.quaternion_subgroup_iff (d.right.map a.toMonoidHom)).mp
      ⟨(a.subgroupMap d.right).symm.trans d.right_model.some⟩ with hh | hh
    · have he : d.right=d.left := map_injective a.injective (hh.trans hL.symm)
      have hi := d.intersection_card
      rw [he,inf_idem] at hi
      have hc : Nat.card d.left = 8 := by
        rw [Nat.card_congr d.left_model.some.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
      omega
    · exact hh
  exact ⟨hL,hR,fun hb=>hl (d.quotientWreathAction_left_one_of_inner a hs hb),
    fun hb=>hr (d.quotientWreathAction_right_one_of_inner a hs hb)⟩

end Subgroup.QuaternionCentralProductData
