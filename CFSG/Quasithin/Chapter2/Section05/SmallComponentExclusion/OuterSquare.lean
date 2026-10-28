module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterCoreTwo
public import Theory.GroupTheory.NormalizerSquareOfInvolutionProduct
/-!
# The outer lift squares to the original central involution

The action kernel is ⟨t⟩, so the square of the lift is z or tz. Its local
centralizer is ⟨t,y⟩. The crossing normalizes the square line ⟨y²⟩ and fixes z,
while carrying t to tz. Hence it cannot preserve the alternative y²=tz.
All actions and elements are those of the original source tuple.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z x : G}

theorem linear_three_outer_lift_square
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (t : G) (ht : orderOf t=2) (htC : t∈twoCore H)
    (htZ : t∈centerIn ((S : Subgroup H).map H.subtype))
    (hZ : IsKleinFour (centerIn ((S : Subgroup H).map H.subtype)))
    (k : K) (hkz : (k : G)=z)
    (y : H) (hyS : y∈S)
    (hy2 : (MathieuSourceSetup.componentAction c y)^2=MulAut.conj k)
    (hker : (MathieuSourceSetup.componentAction c).ker=(zpowers t).subgroupOf H)
    (hC : (S : Subgroup H).map H.subtype ⊓
      centralizer ((GLTwoThreeLocal.residual k).map K.subtype : Set G)=zpowers t ⊔ zpowers (y:G))
    (hxT : x∈c.T) (hxS : x∉(S : Subgroup H).map H.subtype)
    (hxN : x∈normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hxR : x∈centralizer ((GLTwoThreeLocal.residual k).map K.subtype : Set G)) :
    (y:G)^2=z := by
  classical
  let Y := (S : Subgroup H).map H.subtype
  let α := MathieuSourceSetup.componentAction c
  let kH : H := ⟨k,c.component_le k.property⟩
  have hka : α kH = MulAut.conj k := by ext r; rfl
  have hd : y^2*kH⁻¹∈α.ker := by
    change α (y^2*kH⁻¹)=1
    rw [map_mul,map_pow,map_inv,hka,hy2,mul_inv_cancel]
  rw [hker] at hd
  change (y:G)^2*(k:G)⁻¹∈zpowers t at hd
  rw [hkz,mem_zpowers_iff_mem_range_orderOf,ht] at hd
  have hycase : (y:G)^2=z ∨ (y:G)^2=t*z := by
    have hh : (y:G)^2*z⁻¹=1 ∨ (y:G)^2*z⁻¹=t := by
      obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hd
      have hn' : n<2 := Finset.mem_range.mp hn
      interval_cases n
      · exact Or.inl (by simpa only [pow_zero] using he.symm)
      · exact Or.inr (by simpa only [pow_one] using he.symm)
    rcases hh with hh | hh
    · exact Or.inl (mul_inv_eq_one.mp hh)
    · exact Or.inr (mul_inv_eq_iff_eq_mul.mp hh)
  rcases hycase with he | he
  · exact he
  exfalso
  have ht2 : t^2=1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hyt : Commute t (y:G) := (htZ.2 y (mem_map_of_mem H.subtype hyS)).symm
  have hxC : x∈normalizer ((zpowers t ⊔ zpowers (y:G) : Subgroup G):Set G) := by
    rw [← hC]
    exact inf_normalizer_le_normalizer_inf
      ⟨hxN,(centralizer ((GLTwoThreeLocal.residual k).map K.subtype : Set G)).le_normalizer hxR⟩
  have hxline := normalizer_le_normalizer_square_line_of_involution_product t (y:G) ht2 hyt hxC
  have htz : Commute t z := by
    have hzT : z∈centerIn (c.T:Subgroup G) := by
      simpa only [centerIn_eq_map_center] using c.mem_center
    exact hzT.2 t (c.sylow_lt.le htZ.1)
  have hz2 : z^2=1 := by rw [← c.involution]; exact pow_orderOf_eq_one z
  have hy22 : ((y:G)^2)^2=1 := by rw [he,htz.mul_pow,ht2,hz2,one_mul]
  have htzne : t*z≠1 := by
    intro h
    have htzeq : t=z := by
      have hh := congrArg (fun a:G=>a*z) h
      simpa only [mul_assoc,← pow_two,hz2,mul_one,one_mul] using hh
    have hc := MathieuSourceSetup.central_core_involution_not_mem_center_ambient c hgen t ht htC htZ
    apply hc
    rw [htzeq,centerIn_eq_map_center]
    exact c.mem_center
  have hoy : orderOf ((y:G)^2)=2 := orderOf_eq_prime hy22 (he ▸ htzne)
  rw [normalizer_zpowers_eq_centralizer_of_order_two _ hoy] at hxline
  have hfix : x⁻¹*((y:G)^2)*x=(y:G)^2 := by
    have hh := mem_centralizer_singleton_iff.mp hxline
    calc x⁻¹*((y:G)^2)*x = x⁻¹*(((y:G)^2)*x) := mul_assoc _ _ _
         _ = x⁻¹*(x*((y:G)^2)) := by rw [hh]
         _ = (y:G)^2 := inv_mul_cancel_left _ _
  have hcross := (MathieuSourceSetup.source_crossing_on_center c hgen t ht htC htZ hZ).2 x hxT hxN hxS
  have hzfix : x⁻¹*z*x=z := by
    have hzT : z∈centerIn (c.T:Subgroup G) := by
      simpa only [centerIn_eq_map_center] using c.mem_center
    have hh := hzT.2 x hxT
    calc x⁻¹*z*x = x⁻¹*(z*x) := mul_assoc _ _ _
         _ = x⁻¹*(x*z) := by rw [hh]
         _ = z := inv_mul_cancel_left _ _
  have hefix : x⁻¹*(t*z)*x=(x⁻¹*t*x)*(x⁻¹*z*x) := by group
  rw [he,hefix,hcross,hzfix,mul_assoc,← pow_two,hz2,mul_one] at hfix
  have hz1 : z=1 := (mul_left_cancel (a:=t) (hfix.symm.trans (mul_one t).symm))
  have ho := c.involution
  rw [hz1,orderOf_one] at ho
  omega
end CFSG.Quasithin.Chapter2.Section05
