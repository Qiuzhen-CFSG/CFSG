module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FactorCoordinates
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Lifts
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolutionLift
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.TransvectionCoset

/-!
# Involutory quaternion-product transvections

An involution of the actual central-quotient square space with odd factor sign
preserves both embedded quaternion factors and acts trivially on exactly one
of their quotient planes. On the other factor the quaternion lifting theorem
provides an involutory representative with the same central-quotient action.
Gluing this with the identity on the first factor gives a whole-group
involution. Its moving factor restriction is outer, since otherwise the whole
map would be inner and its quotient action trivial.

The action, factors and quotient maps are those of the original intrinsic
central product. Source: Aschbacher–Smith (2.4.29), printed p.546.
-/

public section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

omit [Finite Q] in
private theorem hom_eq_of_factors {P : Type*} [Group P] (f g : Q →* P)
    (hL : ∀ x : d.left, f x = g x) (hR : ∀ x : d.right, f x = g x) : f = g := by
  have hh : d.left ⊔ d.right ≤ f.eqLocus g :=
    sup_le (fun x hx => hL ⟨x,hx⟩) (fun x hx => hR ⟨x,hx⟩)
  rw [d.span] at hh
  ext x
  exact hh (mem_top x)

private theorem quotientWreathAction_eq_iff (a b : MulAut Q) :
    d.quotientWreathAction a = d.quotientWreathAction b ↔
      quotientAut (center Q) a = quotientAut (center Q) b := by
  constructor
  · intro h
    have hs : d.squareIsometryAction a = d.squareIsometryAction b :=
      d.squareIsometriesEquivWreath.injective (by simpa only [d.quotientWreathAction_eq] using h)
    ext v
    have hh := congrArg (fun z : d.squareIsometries => z.val (Additive.ofMul v)) hs
    rw [d.squareIsometryAction_apply, d.squareIsometryAction_apply] at hh
    exact congrArg Additive.toMul hh
  · intro h
    rw [d.quotientWreathAction_eq, d.quotientWreathAction_eq]
    congr 1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [show v = Additive.ofMul v.toMul from rfl, d.squareIsometryAction_apply,
      d.squareIsometryAction_apply, h]

private theorem quotient_square (a : MulAut Q)
    (ha : (d.quotientWreathAction a)^2=1) :
    ∀ x : Q, x⁻¹ * a (a x) ∈ center Q := by
  have he : quotientAut (center Q) (a^2) = 1 := by
    have hw : d.quotientWreathAction (a^2) = d.quotientWreathAction 1 := by
      rw [map_pow, ha, map_one]
    simpa only [map_one] using (d.quotientWreathAction_eq_iff (a^2) 1).mp hw
  intro x
  have hh := DFunLike.congr_fun he (QuotientGroup.mk' (center Q) x)
  rw [quotientAut_apply_mk] at hh
  exact QuotientGroup.eq.mp hh.symm

omit [Finite Q] in
private theorem central_in_subgroup (B : Subgroup Q) (x : B) (hx : (x:Q)∈center Q) :
    x∈center B := by
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp hx y

private theorem left_center : (center d.left).map d.left.subtype = center Q := by
  rw [← intersection_eq_factor_center d.left d.right d.left_model d.intersection_card
    d.commute, d.center_eq]

private theorem right_center : (center d.right).map d.right.subtype = center Q := by
  rw [← intersection_eq_factor_center d.right d.left d.right_model
    (by simpa [inf_comm] using d.intersection_card)
    (fun c hc b hb => (d.commute b hb c hc).symm), inf_comm, d.center_eq]

private theorem left_quotient_fixed (a : MulAut Q)
    (hw : (d.quotientWreathAction a).right=1)
    (hl : (d.quotientWreathAction a).left 1=1) (x : d.left) :
    QuotientGroup.mk' (center Q) (a x) = QuotientGroup.mk' (center Q) x := by
  have hL := (d.quotientWreathAction_right_eq_one_iff a).mp hw
  have hax : a x ∈ d.left := hL.le (mem_map_of_mem a.toMonoidHom x.property)
  have hh := d.quotientWreathAction_apply a (QuotientGroup.mk' (center Q) x) 1
  rw [quotientAut_apply_mk] at hh
  simp only [hw, inv_one, one_mul, hl, BinaryFourPlus.planeLinear_one,
    BinaryFourPlus.coordinate, ite_true] at hh
  change _ = (d.squareCoordinates (Additive.ofMul (QuotientGroup.mk' (center Q) x))).1 at hh
  apply Additive.ofMul.injective
  apply d.squareCoordinates.injective
  exact Prod.ext hh ((d.squareCoordinates_mk_left_zero _ hax).trans
    (d.squareCoordinates_mk_left_zero _ x.property).symm)

private theorem right_quotient_fixed (a : MulAut Q)
    (hw : (d.quotientWreathAction a).right=1)
    (hr : (d.quotientWreathAction a).left BinaryFourPlus.swapIndex=1) (x : d.right) :
    QuotientGroup.mk' (center Q) (a x) = QuotientGroup.mk' (center Q) x := by
  have hL := (d.quotientWreathAction_right_eq_one_iff a).mp hw
  have hR := (d.map_left_eq_iff_map_right_eq a).mp hL
  have hax : a x ∈ d.right := hR.le (mem_map_of_mem a.toMonoidHom x.property)
  have hh := d.quotientWreathAction_apply a (QuotientGroup.mk' (center Q) x)
    BinaryFourPlus.swapIndex
  rw [quotientAut_apply_mk] at hh
  simp only [hw, inv_one, one_mul, hr, BinaryFourPlus.planeLinear_one,
    BinaryFourPlus.coordinate, BinaryFourPlus.swapIndex_ne_one,
    ite_false] at hh
  change _ = (d.squareCoordinates (Additive.ofMul (QuotientGroup.mk' (center Q) x))).2 at hh
  apply Additive.ofMul.injective
  apply d.squareCoordinates.injective
  exact Prod.ext ((d.squareCoordinates_mk_right_zero _ hax).trans
    (d.squareCoordinates_mk_right_zero _ x.property).symm) hh

omit [Finite Q] in
private theorem factor_lift_square (a : MulAut d.left) (b : MulAut d.right)
    (ha : a^2=1) (hb : b^2=1) (β : MulAut Q)
    (hL : ∀x:d.left, β x=(a x:Q)) (hR : ∀x:d.right, β x=(b x:Q)) : β^2=1 := by
  apply MulEquiv.toMonoidHom_injective
  apply d.hom_eq_of_factors
  · intro x
    change β (β x) = (x:Q)
    rw [hL x,hL (a x)]
    exact congrArg Subtype.val (DFunLike.congr_fun ha x)
  · intro x
    change β (β x) = (x:Q)
    rw [hR x,hR (b x)]
    exact congrArg Subtype.val (DFunLike.congr_fun hb x)

private theorem wreath_eq_of_factor_quotients (a b : MulAut Q)
    (hL : ∀x:d.left, QuotientGroup.mk' (center Q) (a x) = QuotientGroup.mk' (center Q) (b x))
    (hR : ∀x:d.right, QuotientGroup.mk' (center Q) (a x) = QuotientGroup.mk' (center Q) (b x)) :
    d.quotientWreathAction a=d.quotientWreathAction b := by
  apply (d.quotientWreathAction_eq_iff a b).mpr
  have hh := d.hom_eq_of_factors
    ((QuotientGroup.mk' (center Q)).comp a.toMonoidHom)
    ((QuotientGroup.mk' (center Q)).comp b.toMonoidHom) hL hR
  ext v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
  rw [quotientAut_apply_mk,quotientAut_apply_mk]
  exact DFunLike.congr_fun hh x

private theorem outer_right_of_wreath_ne_one (β : MulAut Q)
    (hne : d.quotientWreathAction β ≠ 1) (hL : ∀x:d.left, β x=(x:Q)) :
    ¬∃b:d.right, ∀x:d.right, β (x:Q) = ((b*x*b⁻¹:d.right):Q) := by
  rintro ⟨b,hb⟩
  have he : β=MulAut.conj (b:Q) := by
    apply MulEquiv.toMonoidHom_injective
    apply d.hom_eq_of_factors
    · intro x
      change β x = (b:Q)*(x:Q)*(b:Q)⁻¹
      rw [hL x, ← d.commute x x.property b b.property, mul_inv_cancel_right]
    · exact hb
  apply hne
  have hk : MulAut.conj (b:Q)∈d.quotientWreathAction.ker := by
    rw [d.quotientWreathAction_ker]
    exact ⟨b,rfl⟩
  exact he ▸ hk

private theorem outer_left_of_wreath_ne_one (β : MulAut Q)
    (hne : d.quotientWreathAction β ≠ 1) (hR : ∀x:d.right, β x=(x:Q)) :
    ¬∃b:d.left, ∀x:d.left, β (x:Q) = ((b*x*b⁻¹:d.left):Q) := by
  rintro ⟨b,hb⟩
  have he : β=MulAut.conj (b:Q) := by
    apply MulEquiv.toMonoidHom_injective
    apply d.hom_eq_of_factors
    · exact hb
    · intro x
      change β x = (b:Q)*(x:Q)*(b:Q)⁻¹
      rw [hR x, d.commute b b.property x x.property, mul_inv_cancel_right]
  apply hne
  have hk : MulAut.conj (b:Q)∈d.quotientWreathAction.ker := by
    rw [d.quotientWreathAction_ker]
    exact ⟨b,rfl⟩
  exact he ▸ hk

/-- An odd involutory quotient action lifts to an involution fixing precisely
one quaternion factor pointwise and acting outerly on the other. -/
theorem exists_transvection_involution (a : MulAut Q)
    (ha : (d.quotientWreathAction a)^2=1)
    (hs : BinaryFourPlus.factorSign (d.quotientWreathAction a)≠1) :
    ∃β:MulAut Q, d.quotientWreathAction β=d.quotientWreathAction a ∧ β^2=1 ∧
      (((∀x:d.left, β (x:Q)=(x:Q)) ∧
        ¬∃b:d.right, ∀x:d.right, β (x:Q)=((b*x*b⁻¹:d.right):Q)) ∨
       ((∀x:d.right, β (x:Q)=(x:Q)) ∧
        ¬∃b:d.left, ∀x:d.left, β (x:Q)=((b*x*b⁻¹:d.left):Q))) := by
  have hne : d.quotientWreathAction a≠1 := fun h => hs (by rw [h,map_one])
  obtain ⟨hw,hcases⟩ := BinaryFourPlus.TransvectionCoset.involution_coordinates _ ha hs
  have hL := (d.quotientWreathAction_right_eq_one_iff a).mp hw
  have hR := (d.map_left_eq_iff_map_right_eq a).mp hL
  let aL : MulAut d.left := (a.subgroupMap d.left).trans (MulEquiv.subgroupCongr hL)
  let aR : MulAut d.right := (a.subgroupMap d.right).trans (MulEquiv.subgroupCongr hR)
  have hsq := d.quotient_square a ha
  rcases hcases with hl | hr
  · obtain ⟨b,hb,hd⟩ := QuaternionGroup.exists_involution_central_difference_of_equiv
      d.right_model.some aR (fun x => central_in_subgroup d.right _ (hsq x))
    obtain ⟨β,hβL,hβR⟩ := d.exists_factor_lift 1 b
    have hβL' : ∀x:d.left, β (x:Q)=(x:Q) := hβL
    have he : d.quotientWreathAction β=d.quotientWreathAction a := by
      apply d.wreath_eq_of_factor_quotients
      · intro x
        rw [hβL' x]
        exact (d.left_quotient_fixed a hw hl.1 x).symm
      · intro x
        rw [hβR x]
        symm
        apply QuotientGroup.eq.mpr
        exact d.right_center.le ⟨(aR x)⁻¹*b x,hd x,rfl⟩
    exact ⟨β,he,d.factor_lift_square 1 b (by simp) hb β hβL hβR,
      Or.inl ⟨hβL',d.outer_right_of_wreath_ne_one β (he ▸ hne) hβL'⟩⟩
  · obtain ⟨b,hb,hd⟩ := QuaternionGroup.exists_involution_central_difference_of_equiv
      d.left_model.some aL (fun x => central_in_subgroup d.left _ (hsq x))
    obtain ⟨β,hβL,hβR⟩ := d.exists_factor_lift b 1
    have hβR' : ∀x:d.right, β (x:Q)=(x:Q) := hβR
    have he : d.quotientWreathAction β=d.quotientWreathAction a := by
      apply d.wreath_eq_of_factor_quotients
      · intro x
        rw [hβL x]
        symm
        apply QuotientGroup.eq.mpr
        exact d.left_center.le ⟨(aL x)⁻¹*b x,hd x,rfl⟩
      · intro x
        rw [hβR' x]
        exact (d.right_quotient_fixed a hw hr.1 x).symm
    exact ⟨β,he,d.factor_lift_square b 1 hb (by simp) β hβL hβR,
      Or.inr ⟨hβR',d.outer_left_of_wreath_ne_one β (he ▸ hne) hβR'⟩⟩
end Subgroup.QuaternionCentralProductData
