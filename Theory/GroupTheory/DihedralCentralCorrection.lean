module
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupAction.Defs
public import Mathlib.Tactic.Group


/-!
# Splitting the central involution off an order-twelve dihedral pair

For involutions x,t with product of order six, the word z = (x t)^3 is
central in their actual generated subgroup. Replacing t by z t produces
a pair whose product has order three. Recognition of this pair gives a
centerless subgroup R of order six; extracting product coordinates then
identifies the old center with <z> and proves J = Z(J) R with trivial
intersection. The ambient group need not be finite.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
the binary reflection correction in (14.17), printed pp.222--223.
Its literal six-path application is ApartmentExchange/SixPathBinaryReflection.
-/

public section

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem pair_dihedral_three (x u : G) (hx : x*x=1) (hu : u*u=1)
    (horder : orderOf (x*u)=3) :
    Nonempty ((zpowers x ⊔ zpowers u : Subgroup G) ≃* DihedralGroup 3) := by
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_left hx
  have hui : u⁻¹=u := inv_eq_of_mul_eq_one_left hu
  have hxo : orderOf x=2 := by
    apply orderOf_eq_prime (by simpa only [pow_two] using hx)
    intro he
    have huo : orderOf u=3 := by simpa only [he,one_mul] using horder
    have hd := orderOf_dvd_of_pow_eq_one (show u^2=1 by simpa only [pow_two] using hu)
    norm_num [huo] at hd
  have hout : x ∉ zpowers (x*u) := by
    intro hh
    have hd := orderOf_dvd_of_mem_zpowers hh
    norm_num [hxo,horder] at hd
  obtain ⟨_,⟨e⟩⟩ := DihedralGroup.sup_zpowers_equiv_of_inversion (by decide : 0<3)
    (x*u) x horder (by simpa only [pow_two] using hx) hout (by
      simp only [mul_inv_rev,hxi,hui,←mul_assoc,hx,one_mul])
  have heq : zpowers (x*u) ⊔ zpowers x = zpowers x ⊔ zpowers u := by
    apply le_antisymm
    · exact sup_le (zpowers_le.mpr (mul_mem (mem_sup_left (mem_zpowers x))
        (mem_sup_right (mem_zpowers u)))) le_sup_left
    · refine sup_le le_sup_right (zpowers_le.mpr ?_)
      have hh := (zpowers (x*u) ⊔ zpowers x).mul_mem
        (mem_sup_right (mem_zpowers x)) (mem_sup_left (mem_zpowers (x*u)))
      simpa only [←mul_assoc,hx,one_mul] using hh
  exact ⟨(MulEquiv.subgroupCongr heq).symm.trans e⟩

/-- The central involution of a pair with product order six splits off;
the corrected pair generates the actual centerless dihedral group of order six. -/
theorem involutions_product_six_central_correction (x t : G)
    (hx : x*x=1) (ht : t*t=1) (horder : orderOf (x*t)=6) :
    let z := (x*t)^3
    let u := z*t
    let J := zpowers x ⊔ zpowers t
    let R := zpowers x ⊔ zpowers u
    z*z=1 ∧ orderOf z=2 ∧ u*u=1 ∧ orderOf (x*u)=3 ∧
      z∈centerIn J ∧ R≤J ∧
      Nonempty (R ≃* DihedralGroup 3) ∧ centerIn R=⊥ ∧
      centerIn J=zpowers z ∧ centerIn J ⊓ R=⊥ ∧
      J=centerIn J ⊔ R ∧ t=z*u := by
  dsimp only
  let c := x*t
  let z := c^3
  let u := z*t
  let J := zpowers x ⊔ zpowers t
  let R := zpowers x ⊔ zpowers u
  have hc6 : c^6=1 := horder ▸ pow_orderOf_eq_one c
  have hz2 : z*z=1 := by
    change c^3*c^3=1
    rw [←pow_add]
    exact hc6
  have hzo : orderOf z=2 := by
    change orderOf (c^3)=2
    rw [orderOf_pow_of_dvd (by decide : 3≠0) (by rw [horder]; decide),horder]
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_left hx
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left ht
  have hzi : z⁻¹=z := inv_eq_of_mul_eq_one_left hz2
  have hxc : x*c*x⁻¹=c⁻¹ := by
    dsimp [c]
    simp only [mul_inv_rev,hxi,hti,←mul_assoc,hx,one_mul]
  have htc : t*c*t⁻¹=c⁻¹ := by
    dsimp [c]
    simp only [mul_inv_rev,hxi,hti,mul_assoc,ht,mul_one]
  have hzx : Commute z x := by
    have he : x*z*x⁻¹=z := by
      change x*c^3*x⁻¹=z
      rw [←conj_pow,hxc,inv_pow]
      exact hzi
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hzt : Commute z t := by
    have he : t*z*t⁻¹=z := by
      change t*c^3*t⁻¹=z
      rw [←conj_pow,htc,inv_pow]
      exact hzi
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hzJ : z∈J := J.pow_mem (J.mul_mem (mem_sup_left (mem_zpowers x))
    (mem_sup_right (mem_zpowers t))) 3
  have hJz : J≤centralizer ({z}:Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzx.symm.eq))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzt.symm.eq))
  have hzcenter : z∈centerIn J := ⟨hzJ,fun y hy =>
    (mem_centralizer_singleton_iff.mp (hJz hy))⟩
  have hu2 : u*u=1 := by
    change (z*t)*(z*t)=1
    rw [show (z*t)*(z*t)=(z*z)*(t*t) from by
      simpa only [pow_two] using hzt.mul_pow 2,hz2,ht,one_mul]
  have hxu : x*u=c^4 := by
    change x*(z*t)=c^4
    rw [←mul_assoc,←hzx.eq,mul_assoc]
    change c^3*c=c^4
    exact (pow_succ c 3).symm
  have hxuo : orderOf (x*u)=3 := by
    rw [hxu,orderOf_pow' c (by decide : 4≠0),horder]
    decide
  have huJ : u∈J := J.mul_mem hzJ (mem_sup_right (mem_zpowers t))
  have hRJ : R≤J := sup_le le_sup_left (zpowers_le.mpr huJ)
  obtain ⟨e⟩ := pair_dihedral_three x u hx hu2 hxuo
  have hZR : centerIn R=⊥ := by
    rw [centerIn_eq_map_center]
    have he : center R=⊥ := by
      apply bot_unique
      intro y hy
      have hh : e y∈center (DihedralGroup 3) :=
        (centerCongr e ⟨y,hy⟩).property
      rw [DihedralGroup.center_eq_bot_of_odd_ne_one (by decide) (by decide)] at hh
      exact e.injective (hh.trans e.map_one.symm)
    rw [he,Subgroup.map_bot]
  have hdis : centerIn J ⊓ R=⊥ := by
    apply bot_unique
    intro y hy
    exact hZR.le ⟨hy.2,centralizer_le hRJ hy.1.2⟩
  have htu : t=z*u := by
    change t=z*(z*t)
    rw [←mul_assoc,hz2,one_mul]
  have hjoin : J=zpowers z ⊔ R := by
    apply le_antisymm
    · refine sup_le (le_sup_left.trans le_sup_right) (zpowers_le.mpr ?_)
      rw [htu]
      exact mul_mem (mem_sup_left (mem_zpowers z))
        (mem_sup_right (mem_sup_right (mem_zpowers u)))
    · exact sup_le (zpowers_le.mpr hzJ) hRJ
  have hC : zpowers z≤centerIn J := zpowers_le.mpr hzcenter
  have hcenter : centerIn J=zpowers z := by
    apply le_antisymm ?_ hC
    intro y hy
    have hCyR : zpowers z≤centralizer (R:Set G) :=
      hC.trans (inf_le_right.trans (centralizer_le hRJ))
    have hprod : y∈(zpowers z:Set G)*(R:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _
        (hCyR.trans (centralizer_le_normalizer _)),←hjoin]
      exact hy.1
    obtain ⟨v,hv,w,hw,hvw⟩ := hprod
    have hwZ : w∈centerIn J := by
      have he : w=v⁻¹*y := by rw [←hvw,inv_mul_cancel_left]
      rw [he]
      exact (centerIn J).mul_mem ((centerIn J).inv_mem (hC hv)) hy
    have hw1 : w=1 := hdis.le ⟨hwZ,hw⟩
    have hvy : v=y := by simpa only [hw1,mul_one] using hvw
    exact hvy ▸ hv
  exact ⟨hz2,hzo,hu2,hxuo,hzcenter,hRJ,⟨e⟩,hZR,hcenter,hdis,
    by rw [hcenter]; exact hjoin,htu⟩
end Theory.GroupTheory
