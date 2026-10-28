module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryNative

/-!
# Checked products in the native Held commuting graph

On each compatible pair, the proposed product index agrees on the faithful
four-point base with multiplication of the original Sylow words. This is
exact multiplication for every pair used by the elementary-subgroup checker.
Source: the original ATLAS carrier and Aschbacher--Smith 12.7.5, p.840.
-/

public section
namespace Held.OrdinaryElementary.NativeCoverage
open Subgroup Held.InvolutionFixedData.Coverage

private def ProductRow (v : Fin 192) : Prop := ∀w:Fin 192,
  compatible v w = true → ∀k:Fin 4,
    normalPerm (vertexIndex v) (normalPerm (vertexIndex w) ⟨k.val,by omega⟩) =
      normalPerm (vertexIndex (productVertex v w)) ⟨k.val,by omega⟩

set_option maxRecDepth 10000 in
private theorem product_row_0 : ∀j:Fin 4, ProductRow ⟨0+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_1 : ∀j:Fin 4, ProductRow ⟨4+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_2 : ∀j:Fin 4, ProductRow ⟨8+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_3 : ∀j:Fin 4, ProductRow ⟨12+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_4 : ∀j:Fin 4, ProductRow ⟨16+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_5 : ∀j:Fin 4, ProductRow ⟨20+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_6 : ∀j:Fin 4, ProductRow ⟨24+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_7 : ∀j:Fin 4, ProductRow ⟨28+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_8 : ∀j:Fin 4, ProductRow ⟨32+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_9 : ∀j:Fin 4, ProductRow ⟨36+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_10 : ∀j:Fin 4, ProductRow ⟨40+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_11 : ∀j:Fin 4, ProductRow ⟨44+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_12 : ∀j:Fin 4, ProductRow ⟨48+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_13 : ∀j:Fin 4, ProductRow ⟨52+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_14 : ∀j:Fin 4, ProductRow ⟨56+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_15 : ∀j:Fin 4, ProductRow ⟨60+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_16 : ∀j:Fin 4, ProductRow ⟨64+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_17 : ∀j:Fin 4, ProductRow ⟨68+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_18 : ∀j:Fin 4, ProductRow ⟨72+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_19 : ∀j:Fin 4, ProductRow ⟨76+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_20 : ∀j:Fin 4, ProductRow ⟨80+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_21 : ∀j:Fin 4, ProductRow ⟨84+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_22 : ∀j:Fin 4, ProductRow ⟨88+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_23 : ∀j:Fin 4, ProductRow ⟨92+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_24 : ∀j:Fin 4, ProductRow ⟨96+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_25 : ∀j:Fin 4, ProductRow ⟨100+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_26 : ∀j:Fin 4, ProductRow ⟨104+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_27 : ∀j:Fin 4, ProductRow ⟨108+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_28 : ∀j:Fin 4, ProductRow ⟨112+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_29 : ∀j:Fin 4, ProductRow ⟨116+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_30 : ∀j:Fin 4, ProductRow ⟨120+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_31 : ∀j:Fin 4, ProductRow ⟨124+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_32 : ∀j:Fin 4, ProductRow ⟨128+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_33 : ∀j:Fin 4, ProductRow ⟨132+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_34 : ∀j:Fin 4, ProductRow ⟨136+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_35 : ∀j:Fin 4, ProductRow ⟨140+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_36 : ∀j:Fin 4, ProductRow ⟨144+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_37 : ∀j:Fin 4, ProductRow ⟨148+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_38 : ∀j:Fin 4, ProductRow ⟨152+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_39 : ∀j:Fin 4, ProductRow ⟨156+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_40 : ∀j:Fin 4, ProductRow ⟨160+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_41 : ∀j:Fin 4, ProductRow ⟨164+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_42 : ∀j:Fin 4, ProductRow ⟨168+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_43 : ∀j:Fin 4, ProductRow ⟨172+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_44 : ∀j:Fin 4, ProductRow ⟨176+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_45 : ∀j:Fin 4, ProductRow ⟨180+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_46 : ∀j:Fin 4, ProductRow ⟨184+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

set_option maxRecDepth 10000 in
private theorem product_row_47 : ∀j:Fin 4, ProductRow ⟨188+j.val,by omega⟩ := by
  unfold ProductRow
  decide +kernel

private theorem product_checked (v w : Fin 192) (hc : compatible v w=true) (k:Fin 4) :
    normalPerm (vertexIndex v) (normalPerm (vertexIndex w) ⟨k.val,by omega⟩) =
      normalPerm (vertexIndex (productVertex v w)) ⟨k.val,by omega⟩ := by
  have blocks : ∀ j : Fin 48, ∀ r : Fin 4, ProductRow ⟨4*j.val+r.val,by omega⟩ := by
    intro j
    fin_cases j
    · exact product_row_0
    · exact product_row_1
    · exact product_row_2
    · exact product_row_3
    · exact product_row_4
    · exact product_row_5
    · exact product_row_6
    · exact product_row_7
    · exact product_row_8
    · exact product_row_9
    · exact product_row_10
    · exact product_row_11
    · exact product_row_12
    · exact product_row_13
    · exact product_row_14
    · exact product_row_15
    · exact product_row_16
    · exact product_row_17
    · exact product_row_18
    · exact product_row_19
    · exact product_row_20
    · exact product_row_21
    · exact product_row_22
    · exact product_row_23
    · exact product_row_24
    · exact product_row_25
    · exact product_row_26
    · exact product_row_27
    · exact product_row_28
    · exact product_row_29
    · exact product_row_30
    · exact product_row_31
    · exact product_row_32
    · exact product_row_33
    · exact product_row_34
    · exact product_row_35
    · exact product_row_36
    · exact product_row_37
    · exact product_row_38
    · exact product_row_39
    · exact product_row_40
    · exact product_row_41
    · exact product_row_42
    · exact product_row_43
    · exact product_row_44
    · exact product_row_45
    · exact product_row_46
    · exact product_row_47
  have hh := blocks ⟨v.val/4,by omega⟩ ⟨v.val%4,by omega⟩
  have he : (⟨4*(v.val/4)+v.val%4,by omega⟩ : Fin 192) = v := by
    apply Fin.ext
    change 4*(v.val/4)+v.val%4=v.val
    omega
  rw [he] at hh
  exact hh w hc k

/-- Exact product of the two literal Sylow words for every compatible pair. -/
theorem native_product (v w : Fin 192) (hc : compatible v w = true) :
    native (productVertex v w) = native v * native w := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  intro k
  simp only [native,Subgroup.coe_mul,map_mul,Equiv.Perm.mul_apply,
    normalForm_representation]
  exact (product_checked v w hc k).symm

end Held.OrdinaryElementary.NativeCoverage
