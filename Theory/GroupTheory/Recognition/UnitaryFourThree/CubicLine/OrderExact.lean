module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.OrderBound
public import Theory.GroupAction.QuaternionSixteenInvertedSection

/-!
# The order243 odd core and its actual elementary central quotient

The actual quaternion Sylow can be marked at the original z. Its action
on D/W and the central-displacement count force D to have order243 and
D/W to be elementary of order81. The source consumer retains only the
earlier reflected actors and the separately owned U-line normalizer data.
No faithful action, quotient module model or numerical conclusion is assumed.
Source: Aschbacher, Sporadic Groups (1994),45.8,printed p246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace CubicLine
omit [Finite G] in
theorem line_normal (W:Subgroup G) (hW:Nat.card W=3) :
    (W.subgroupOf (oddKernel W)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (le_oddKernel W hW)).mpr
    (map_subtype_le _)
end CubicLine
namespace IsType
variable (h:IsType z)
include h in
theorem cubic_line_oddKernel_order_exact (W:Subgroup G) (hW:Nat.card W=3)
    (hWH:W≤centralizer z)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hS:∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4))
    (hD:Nat.card (CubicLine.oddKernel W)∣243) (hlo:27≤Nat.card (CubicLine.oddKernel W)) :
    letI: (W.subgroupOf (CubicLine.oddKernel W)).Normal:=CubicLine.line_normal W hW
    Nat.card (CubicLine.oddKernel W)=243 ∧
      Nat.card ((CubicLine.oddKernel W)⧸W.subgroupOf (CubicLine.oddKernel W))=81 ∧
      IsElementaryAbelian 3 ((CubicLine.oddKernel W)⧸W.subgroupOf (CubicLine.oddKernel W)) := by
  let : (W.subgroupOf (CubicLine.oddKernel W)).Normal:=CubicLine.line_normal W hW
  obtain ⟨P,hP⟩:=hS
  have hzN:z∈normalizer (W:Set G):=centralizer_le_normalizer _
    (fun w hw=>mem_centralizer_singleton_iff.mp (hWH hw))
  obtain ⟨S,hSe,hSN,hzS⟩:=exists_marked_quaternion_subgroup (normalizer (W:Set G)) z hzN h.involution P hP
  exact quaternion_inverted_section_order S (CubicLine.oddKernel W) W hSe.some z hzS h.involution
    (hSN.trans (CubicLine.normalizer_normalizes_oddKernel W)) hSN
    (CubicLine.le_oddKernel W hW) hW hD hlo
    (h.cubic_line_oddKernel_inversion W hW hWH hfixed).1

include h in
theorem source_cubic_line_order_exact_of_moved_line (P:Sylow 3 (centralizer z))
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
    letI: (W.subgroupOf (CubicLine.oddKernel W)).Normal:=CubicLine.line_normal W hW
    Nat.card (CubicLine.oddKernel W)=243 ∧
      Nat.card ((CubicLine.oddKernel W)⧸W.subgroupOf (CubicLine.oddKernel W))=81 ∧
      IsElementaryAbelian 3 ((CubicLine.oddKernel W)⧸W.subgroupOf (CubicLine.oddKernel W)) := by
  have hc:=h.source_cubic_line_card_dvd_of_binary_normalizers P m W F hW hWX hfixed hsplit
    hF hFV hFD hVN hindex
  obtain ⟨hV,hVc⟩:=h.reflected_kernel_of_source_binary_normalizers P m
  have hcap:Nat.card (CubicNormalizer.oddKernel
      ((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓CubicLine.oddKernel W:Subgroup G)=27:=
    (h.cubic_line_kernel_intersection _ W (h.cubic_sylow_image_card P) (map_subtype_le _)
      hW hWX hfixed hsplit hV hVc).2
  exact h.cubic_line_oddKernel_order_exact W hW (hWX.trans (map_subtype_le _)) hfixed hS hc
    (hcap ▸ card_le_of_le inf_le_right)
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
