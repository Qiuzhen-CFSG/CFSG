module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.OrderExact
public import Theory.GroupTheory.CubicQuaternionExtraspecial

/-!
# The original extraspecial odd core of order243

The actual moved cubic line and its order24 normalizer quotient exclude an
abelian odd core. The quaternion action fixes its center to be exactly W,
and the original z action gives exponent three. Thus the source core is
extraspecial of order243, on its original carrier and with the marked center.
The U-line normalizer facts remain with their independent source producer.
Source: Aschbacher, Sporadic Groups (1994),45.8,printed p246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_extraspecial (W:Subgroup G) (hW:Nat.card W=3) (hWH:W≤centralizer z)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hS:∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4))
    (hD:Nat.card (CubicLine.oddKernel W)=243)
    (hne:¬CubicLine.oddKernel W≤Subgroup.centralizer (CubicLine.oddKernel W:Set G))
    [(W.subgroupOf (CubicLine.oddKernel W)).Normal]
    [IsElementaryAbelian 3 ((CubicLine.oddKernel W)⧸W.subgroupOf (CubicLine.oddKernel W))] :
    (center (CubicLine.oddKernel W)).map (CubicLine.oddKernel W).subtype=W ∧
      IsExtraspecial 3 (CubicLine.oddKernel W) ∧ ∀d∈CubicLine.oddKernel W,d^3=1 := by
  let D:=CubicLine.oddKernel W
  let K:=W.subgroupOf D
  have hWD:W≤D:=CubicLine.le_oddKernel W hW
  have hcW:W≤Subgroup.centralizer (D:Set G):=le_centralizer_iff.mp (CubicLine.oddKernel_centralizes W hW)
  have hzN:z∈normalizer (W:Set G):=centralizer_le_normalizer _
    (fun w hw=>mem_centralizer_singleton_iff.mp (hWH hw))
  obtain ⟨P,hP⟩:=hS
  obtain ⟨S,hSe,hSN,hzS⟩:=exists_marked_quaternion_subgroup (normalizer (W:Set G)) z hzN h.involution P hP
  have hi:=h.cubic_line_oddKernel_inversion W hW hWH hfixed
  have hcenter:(center D).map D.subtype=W:=quaternion_inverted_section_center S D W hSe.some z
    hzS h.involution (hSN.trans (CubicLine.normalizer_normalizes_oddKernel W)) hSN hWD hW hcW hD hne hi.1
  have hce:center D=K:=by
    apply map_injective D.subtype_injective
    rw [hcenter,map_subgroupOf_eq_of_le hWD]
  have hcc:Nat.card (center D)=3:=by
    rw [hce,Nat.card_congr (subgroupOfEquivOfLe hWD).toEquiv,hW]
  have hqe:IsElementaryAbelian 3 (D⧸center D):=by
    let e:=QuotientGroup.quotientMulEquivOfEq hce
    exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hqc:Nat.card (D⧸center D)=81:=by
    have hh:=card_eq_card_quotient_mul_card_subgroup (center D)
    rw [hD,hcc] at hh
    omega
  have he:IsExtraspecial 3 D:={
    center_order_p:=hcc
    quotient_elementary_abelian:=hqe
    quotient_nontrivial:=Finite.one_lt_card_iff_nontrivial.mp (by omega) }
  have hzD:z∈normalizer (D:Set G):=CubicLine.normalizer_normalizes_oddKernel W hzN
  let a:=D.normalizerMonoidHom ⟨z,hzD⟩
  have hKc:Nat.card K=3:=by rw [Nat.card_congr (subgroupOfEquivOfLe hWD).toEquiv,hW]
  have haf:∀c∈K,a c=c:=by
    intro c hc
    apply Subtype.ext
    change z*(c:G)*z⁻¹=(c:G)
    have hh:(c:G)*z=z*(c:G):=mem_centralizer_singleton_iff.mp (hWH hc)
    rw [←hh,mul_inv_cancel_right]
  have hai:∀d:D,a d*d∈K:=fun d=>hi.1 d d.property
  have hp:=a.exponent_three_of_fixed_cubic_inverted_quotient K hKc hce.ge haf hai
  refine ⟨hcenter,he,?_⟩
  intro d hd
  exact congrArg Subtype.val (hp ⟨d,hd⟩)
include h in
theorem source_cubic_line_extraspecial_of_moved_line (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (W F:Subgroup G) (hW:Nat.card W=3)
    (hWX:W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hsplit:normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z))
    (hS:∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4))
    (hF:Nat.card F=3)
    (hFV:F≤CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hFD:F≤CubicLine.oddKernel W)
    (hVN:normalizer (F:Set G)≤normalizer
      (CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype):Set G))
    (hindex:(CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)).relIndex
      (normalizer (F:Set G))=24) :
    Nat.card (CubicLine.oddKernel W)=243 ∧
      (center (CubicLine.oddKernel W)).map (CubicLine.oddKernel W).subtype=W ∧
      IsExtraspecial 3 (CubicLine.oddKernel W) ∧ ∀d∈CubicLine.oddKernel W,d^3=1 := by
  let : (W.subgroupOf (CubicLine.oddKernel W)).Normal:=CubicLine.line_normal W hW
  obtain ⟨hD,_,hqe⟩:=h.source_cubic_line_order_exact_of_moved_line P m W F hW hWX hfixed hsplit hS
    hF hFV hFD hVN hindex
  let : IsElementaryAbelian 3 ((CubicLine.oddKernel W)⧸W.subgroupOf (CubicLine.oddKernel W)):=hqe
  obtain ⟨hV,hVc⟩:=h.reflected_kernel_of_source_binary_normalizers P m
  let : IsElementaryAbelian 3 (CubicNormalizer.oddKernel
      ((P:Subgroup (centralizer z)).map (centralizer z).subtype)):=hV
  have hVF:CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)≤
      Subgroup.centralizer (F:Set G):=by
    intro v hv f hf
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M:=CubicNormalizer.oddKernel
      ((P:Subgroup (centralizer z)).map (centralizer z).subtype))).comm
      (⟨f,hFV hf⟩:CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) ⟨v,hv⟩)
  have hcap:Nat.card (CubicLine.oddKernel W⊓CubicNormalizer.oddKernel
      ((P:Subgroup (centralizer z)).map (centralizer z).subtype):Subgroup G)=27:=by
    rw [inf_comm]
    exact (h.cubic_line_kernel_intersection _ W (h.cubic_sylow_image_card P) (map_subtype_le _)
      hW hWX hfixed hsplit hV hVc).2
  have hne:=nonabelian_of_odd_centralizer_quotient (CubicLine.oddKernel W)
    (CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) F
    hD hVF hFD hVN hindex hcap
  exact ⟨hD,h.cubic_line_extraspecial W hW (hWX.trans (map_subtype_le _)) hfixed hS hD hne⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
