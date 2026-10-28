module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Outer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.ComponentFixer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction.Definitions
public import Theory.GroupAction.PerfectCentralQuotient

/-! The genuine outer J₂ involution class supplies coboundaries, with
conjugators in J₂ because the outer quotient has order two. Source2.5.19(4). -/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
open Sporadic.LeechRelated.J2
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

private theorem inner_conjugator_of_index_two {A : Type*} [Group A]
    (H : Subgroup A) (hindex : H.index = 2) (a b : A) (ha : a ∉ H)
    (h : IsConj a b) : ∃ v ∈ H, v * a * v⁻¹ = b := by
  obtain ⟨u,hu⟩ := isConj_iff.mp h
  by_cases hum : u ∈ H
  · exact ⟨u,hum,hu⟩
  · refine ⟨u*a,?_,?_⟩
    · exact (mul_mem_iff_of_index_two hindex).mpr (by simp [hum,ha])
    · simpa only [mul_inv_rev] using (show u*a*a*(a⁻¹*u⁻¹)=b from by
        calc
          u*a*a*(a⁻¹*u⁻¹)=u*a*u⁻¹ := by group
          _ = b := hu)

/-- Every fixed involution is a coboundary for an actual outer J₂ actor. -/
theorem j2_outer_fixed_involution_coboundary
    (a : MulAut Carrier) (ha : orderOf a = 2)
    (ho : ¬ ∃ y : Carrier, a = MulAut.conj y)
    (x : Carrier) (hx : a x = x) (hx2 : x ^ 2 = 1) :
    ∃ w : Carrier, x = w * (a w)⁻¹ := by
  have hao : a ∉ MulAut.innerSubgroup Carrier := by
    rintro ⟨y,hy⟩
    exact ho ⟨y,hy.symm⟩
  have hi : (MulAut.innerSubgroup Carrier).index = 2 := by
    have hlo := (MulAut.innerSubgroup Carrier).one_lt_index_of_ne_top
      (fun h => hao (h ▸ mem_top a))
    have hup := Sporadic.LeechRelated.J2.outer_card_le_two
    change (MulAut.innerSubgroup Carrier).index ≤ 2 at hup
    omega
  let b := MulAut.conj x * a
  have hbo : b ∉ MulAut.innerSubgroup Carrier := by
    intro hb
    have h := (MulAut.innerSubgroup Carrier).mul_mem
      (inv_mem (show MulAut.conj x ∈ MulAut.innerSubgroup Carrier from ⟨x,rfl⟩)) hb
    exact hao (by simpa only [b,inv_mul_cancel_left] using h)
  have hb2 : b ^ 2 = 1 := by
    apply MulEquiv.ext
    intro y
    have ha2 : a (a y) = y := by
      have h := congrArg (fun f : MulAut Carrier => f y) (ha ▸ pow_orderOf_eq_one a)
      simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using h
    change x * a (x * a y * x⁻¹) * x⁻¹ = y
    rw [map_mul,map_mul,map_inv,hx,ha2]
    have hh : x*x=1 := by simpa only [pow_two] using hx2
    calc
      x * (x*y*x⁻¹) * x⁻¹ = (x*x)*y*(x*x)⁻¹ := by group
      _ = y := by rw [hh]; simp
  have hbn : b ≠ 1 := fun h => hbo (h ▸ one_mem _)
  have hb : orderOf b = 2 := orderOf_eq_prime hb2 hbn
  have hconj : IsConj a b := (J2Outer.outer_involution_fusion a ha ho).symm.trans
    (J2Outer.outer_involution_fusion b hb (by rintro ⟨y,hy⟩; exact hbo ⟨y,hy.symm⟩))
  obtain ⟨v,⟨w,hw⟩,hv⟩ := inner_conjugator_of_index_two
    (MulAut.innerSubgroup Carrier) hi a b hao hconj
  subst v
  refine ⟨w,?_⟩
  apply Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction.inner_conj_injective
  have he : MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹ = MulAut.conj x := by
    rw [hv]
    exact mul_inv_cancel_right _ _
  have hh : MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹ =
      MulAut.conj (w * (a w)⁻¹) := by
    apply MulEquiv.ext
    intro y
    change w * a (w⁻¹ * a.symm y * w) * w⁻¹ =
      (w * (a w)⁻¹) * y * (w * (a w)⁻¹)⁻¹
    rw [map_mul,map_mul,map_inv,a.apply_symm_apply,mul_inv_rev,inv_inv]
    group
  exact he.symm.trans hh

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
