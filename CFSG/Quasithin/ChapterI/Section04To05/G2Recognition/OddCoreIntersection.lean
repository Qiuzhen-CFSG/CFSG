module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.OddCoreExclusions
public import Theory.GroupAction.CentralInversionFixedLift
public import Theory.GroupAction.TernaryCubicFixedCard

/-!
# The common intersection and equal orders of the marked cubic odd cores

Write D and E for the original odd cores of C_G(x) and C_G(y). Then
C_D(y) = ⟨x⟩(D ∩ E), with disjoint factors. To prove the nontrivial
containment, the displacement under the marked central involution belongs
to E by the literal decomposition C_G(y) = E H₁. Its norm belongs to
⟨x⟩, and the exponent-three identity reconstructs the original element.

Fixed points of y on D/⟨x⟩ lift without loss: the central involution
fixes the kernel and inverts the quotient. Consequently their number is
|D ∩ E|. If |D|=27, this number is three. A cubic automorphism of the
opposite elementary quotient of order 81 cannot have just three fixed
points, so |E| cannot be 243. The earlier simultaneous-small-core result
now implies |D|=|E| in all cases. This excludes the mixed 27/243 branch.

Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417; the literal centralizer
and inversion inputs are the q=3 instances of Fong–Wong §3B. This argument
does not use Fong §6C's q>3 invariant-line selection. The pairs (3,3) and
(27,27) and the actual Atlas recognition equivalence remain to be excluded
or constructed. `Chapter14OddCoreIntersection` supplies the source consumer.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

private theorem core_fixed_line (t : CubicTorus c) :
    (cubicOppositeAction c t.x ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩).fixedSubgroup =
      cubicCoreLine c t.x := by
  ext d
  rw [MulAut.mem_fixedSubgroup]
  change (cubicOppositeAction c t.x _ d = d) ↔ (d:G) ∈ zpowers ((t.x:c.H):G)
  constructor
  · intro h
    have he : (t.z:G)*(d:G)*(t.z:G)⁻¹=(d:G) := congrArg Subtype.val h
    exact (cubic_oddCore_fixed c t.x t.x_order).le ⟨d.property, by
      rw [t.centralizer]
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he).symm⟩
  · intro h
    apply Subtype.ext
    have hdH : (d:G) ∈ c.H := (zpowers_le.mpr t.x.val.property) h
    have hc := mem_centralizer_singleton_iff.mp (t.centralizer ▸ hdH)
    change (t.z:G)*(d:G)*(t.z:G)⁻¹=(d:G)
    rw [←hc,mul_inv_cancel_right]

omit [Finite G] in
private theorem opposite_fixes_core_line (t : CubicTorus c) (d : cubicOddCore c t.x)
    (hd : d ∈ cubicCoreLine c t.x) : cubicOppositeAction c t.x t.y d=d := by
  apply Subtype.ext
  have hc : ((t.y:c.H):G) ∈ Subgroup.centralizer (zpowers ((t.x:c.H):G):Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
    exact opposite_factor_le_cubic_centralizer c t.x (mem_map_of_mem c.H.subtype t.y.property)
  change ((t.y:c.H):G)*(d:G)*(((t.y:c.H):G))⁻¹=(d:G)
  rw [←hc d hd,mul_inv_cancel_right]

theorem left_oddCore_fixed_card_formula (t : CubicTorus c) :
    Nat.card (cubicOddCore c t.x ⊓ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G) : Subgroup G)=
      3*Nat.card (cubicOppositeQuotientAction c t.x t.y).fixedSubgroup := by
  let D := cubicOddCore c t.x
  let W := cubicCoreLine c t.x
  let q := QuotientGroup.mk' W
  let z : c.H₂ := ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
  let a := cubicOppositeAction c t.x z
  let b := cubicOppositeAction c t.x t.y
  let β := cubicOppositeQuotientAction c t.x t.y
  have hab : a*b=b*a := by
    rw [←map_mul,←map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.y.val.property)).symm
  have hlift (d : D) (hd : β (q d)=q d) : b d=d := by
    apply MulAut.fixed_of_central_displacement_of_inverted_quotient a b hab W (cubicCoreLine_le_center c t.x)
      (by rw [cubicCoreLine_card c t.x t.x_order]; decide)
      (fun w hw => (MulAut.mem_fixedSubgroup a w).mp ((core_fixed_line t).ge hw))
      (opposite_fixes_core_line t)
      (fun v => (cubic_oddCore_inversion c t.x t.x_order t.z
        ((orderOf_coe t.z).trans t.z_order) t.centralizer).1 v v.property) d
    apply (QuotientGroup.eq_one_iff _).mp
    change q (b d*d⁻¹)=1
    rw [map_mul,map_inv]
    have he : q (b d)=q d := hd
    rw [he,mul_inv_cancel]
  let f : b.fixedSubgroup →* β.fixedSubgroup := {
    toFun d := ⟨q (d:D), by
      rw [MulAut.mem_fixedSubgroup]
      change q (b d)=q d
      rw [(MulAut.mem_fixedSubgroup b d).mp d.property]⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' d e := Subtype.ext (map_mul q (d:D) (e:D)) }
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨d,hd⟩ := QuotientGroup.mk'_surjective W (v:D ⧸ W)
    refine ⟨⟨d,(MulAut.mem_fixedSubgroup b d).mpr (hlift d ?_)⟩,Subtype.ext hd⟩
    rw [hd]
    exact (MulAut.mem_fixedSubgroup β v).mp v.property
  let e : f.ker ≃ W := {
    toFun d := ⟨d.val.val,(QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val d.property)⟩
    invFun w := ⟨⟨w,(MulAut.mem_fixedSubgroup b w).mpr (opposite_fixes_core_line t w w.property)⟩,
      Subtype.ext ((QuotientGroup.eq_one_iff _).mpr w.property)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hker : Nat.card f.ker=3 := (Nat.card_congr e).trans (cubicCoreLine_card c t.x t.x_order)
  have hbcard : Nat.card b.fixedSubgroup=3*Nat.card β.fixedSubgroup := by
    have hh := f.ker.card_mul_index
    rw [hker,index_ker,MonoidHom.range_eq_top.mpr hf,card_top] at hh
    exact hh.symm
  let F := D ⊓ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G)
  have he : b.fixedSubgroup.map D.subtype=F := by
    ext d
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨w.property,?_⟩
      rw [zpowers_eq_closure,centralizer_closure]
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg Subtype.val ((MulAut.mem_fixedSubgroup b w).mp hw)
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hd
      refine ⟨⟨d,hd.1⟩,?_,rfl⟩
      apply (MulAut.mem_fixedSubgroup b _).mpr
      apply Subtype.ext
      change ((t.y:c.H):G)*d*(((t.y:c.H):G))⁻¹=d
      have hh : d*((t.y:c.H):G)=((t.y:c.H):G)*d := by
        have h := hd.2
        rw [zpowers_eq_closure,centralizer_closure] at h
        exact mem_centralizer_singleton_iff.mp h
      rw [←hh,mul_inv_cancel_right]
  change Nat.card F=3*Nat.card β.fixedSubgroup
  rw [←he,card_map_of_injective D.subtype_injective,hbcard]

theorem left_oddCore_twentySeven_fixed_card (t : CubicTorus c) (hcard : Nat.card (cubicOddCore c t.x)=27) :
    Nat.card (cubicOddCore c t.x ⊓ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G) : Subgroup G)=9 := by
  let D := cubicOddCore c t.x
  let W := cubicCoreLine c t.x
  let β := cubicOppositeQuotientAction c t.x t.y
  have hqc : Nat.card (D ⧸ W)=9 := by
    have hh := t.left_oddCore_quotient_card
    rw [hcard] at hh
    change Nat.card (D ⧸ W)*3=27 at hh
    omega
  have hβ3 : β^3=1 := by
    rw [←map_pow,show t.y^3=1 from t.y_order ▸ pow_orderOf_eq_one t.y,map_one]
  have hβne : β≠1 := by
    intro h
    have he := t.left_oddCore_quotient_action_faithful (by omega) (h.trans (map_one _).symm)
    have ho := t.y_order
    rw [he,orderOf_one] at ho
    omega
  rw [left_oddCore_fixed_card_formula t,MulAut.cubic_fixed_card_of_card_nine β hβ3 hβne hqc]

private theorem fixed_displacement_mem_opposite (t : CubicTorus c) (u : G)
    (hu : u ∈ cubicCentralizer (swapFactors c) t.y) :
    (t.z:G)*u*(t.z:G)⁻¹*u⁻¹ ∈ cubicOddCore (swapFactors c) t.y := by
  let E := cubicOddCore (swapFactors c) t.y
  let L := c.H₁.map c.H.subtype
  have hLN : L ≤ normalizer (E:Set G) :=
    (opposite_factor_le_cubic_centralizer (swapFactors c) t.y).trans
      ((cubicCentralizer (swapFactors c) t.y).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _)))
  rw [cubic_centralizer_split (swapFactors c) t.y t.y_order] at hu
  change u ∈ (↑(E ⊔ L):Set G) at hu
  rw [coe_mul_of_right_le_normalizer_left E L hLN] at hu
  obtain ⟨d,hd,l,hl,he⟩ := hu
  have hlH : l ∈ c.H := (map_subtype_le _) hl
  have hzl : (t.z:G)*l=l*(t.z:G) :=
    (mem_centralizer_singleton_iff.mp (t.centralizer ▸ hlH)).symm
  have hzL : (t.z:G) ∈ L := mem_map_of_mem c.H.subtype
    (t.central_line ▸ mem_zpowers t.z).1
  have hzd : (t.z:G)*d*(t.z:G)⁻¹ ∈ E :=
    (mem_normalizer_iff.mp (hLN hzL) d).mp hd
  have hv : (t.z:G)*u*(t.z:G)⁻¹*u⁻¹=((t.z:G)*d*(t.z:G)⁻¹)*d⁻¹ := by
    rw [←he]
    calc
      _ = ((t.z:G)*d*(t.z:G)⁻¹)*
        ((t.z:G)*l*(t.z:G)⁻¹)*l⁻¹*d⁻¹ := by group
      _ = _ := by rw [hzl,mul_inv_cancel_right]; group
  rw [hv]
  exact E.mul_mem hzd (E.inv_mem hd)

theorem left_oddCore_fixed_decomposition (t : CubicTorus c) :
    cubicOddCore c t.x ⊓ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G) =
      zpowers ((t.x:c.H):G) ⊔ (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y) := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let X := zpowers ((t.x:c.H):G)
  let F := D ⊓ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G)
  let K := D ⊓ E
  have hXF : X ≤ F := by
    refine le_inf (cubic_line_le_oddCore c t.x t.x_order) ?_
    apply le_centralizer_iff.mp
    change zpowers ((t.y:c.H):G) ≤ Subgroup.centralizer (zpowers ((t.x:c.H):G):Set G)
    conv_rhs => rw [zpowers_eq_closure,centralizer_closure]
    exact (zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
      (opposite_factor_le_cubic_centralizer c t.x)
  have hKF : K ≤ F := by
    refine le_inf inf_le_left ?_
    rw [zpowers_eq_closure,centralizer_closure]
    exact inf_le_right.trans (map_subtype_le _)
  apply le_antisymm ?_ (sup_le hXF hKF)
  intro u hu
  let v := (t.z:G)*u*(t.z:G)⁻¹*u
  let δ := (t.z:G)*u*(t.z:G)⁻¹*u⁻¹
  have hv : v ∈ X := (cubic_oddCore_inversion c t.x t.x_order t.z
    ((orderOf_coe t.z).trans t.z_order) t.centralizer).1 u hu.1
  have hδD : δ ∈ D := by
    have hh := D.mul_mem ((cubic_line_le_oddCore c t.x t.x_order) hv)
      (D.mul_mem (D.inv_mem hu.1) (D.inv_mem hu.1))
    dsimp only [v] at hh
    change δ ∈ D
    convert hh using 1; dsimp only [δ]; group
  have hδE : δ ∈ E := fixed_displacement_mem_opposite t u (by
    have hh := hu.2
    rwa [zpowers_eq_closure,centralizer_closure] at hh)
  have h3 : u^3=1 := congrArg Subtype.val (t.left_oddCore_cube ⟨u,hu.1⟩)
  have he : v⁻¹*δ=u := by
    have hi : u⁻¹*u⁻¹=u := by
      apply inv_injective
      simp only [mul_inv_rev,inv_inv]
      apply mul_eq_one_iff_eq_inv.mp
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using h3
    calc
      _ = u⁻¹*u⁻¹ := by dsimp only [v,δ]; group
      _ = u := hi
  rw [←he]
  exact (X ⊔ K).mul_mem (mem_sup_left (X.inv_mem hv)) (mem_sup_right ⟨hδD,hδE⟩)

theorem left_oddCore_fixed_intersection_card (t : CubicTorus c) :
    Nat.card (cubicOddCore c t.x ⊓ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G) : Subgroup G)=
      3*Nat.card (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G) := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let X := zpowers ((t.x:c.H):G)
  let K := D ⊓ E
  have hEX : Disjoint E X := by
    apply disjoint_iff.mpr
    exact bot_unique ((inf_le_inf_left E
      (zpowers_le.mpr (mem_map_of_mem c.H.subtype t.x.property))).trans
      (cubic_oddCore_inf_factor (swapFactors c) t.y).le)
  have hDX : D ≤ Subgroup.centralizer (X:Set G) := by
    dsimp only [X]
    rw [zpowers_eq_closure,centralizer_closure]
    exact map_subtype_le _
  rw [left_oddCore_fixed_decomposition t]
  change Nat.card (X ⊔ K : Subgroup G)=3*Nat.card K
  rw [card_sup_eq_mul_of_normalizes_of_disjoint X K
    ((inf_le_left.trans hDX).trans (Subgroup.centralizer_le_normalizer _))
    (hEX.mono_left inf_le_right).symm]
  rw [show Nat.card X=3 from by rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order]]

theorem oddCore_intersection_card_of_twentySeven (t : CubicTorus c)
    (hcard : Nat.card (cubicOddCore c t.x)=27) :
    Nat.card (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G)=3 := by
  have hh := left_oddCore_twentySeven_fixed_card t hcard
  rw [left_oddCore_fixed_intersection_card t] at hh
  omega

theorem left_oddCore_quotient_fixed_card (t : CubicTorus c) :
    Nat.card (cubicOppositeQuotientAction c t.x t.y).fixedSubgroup =
      Nat.card (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G) := by
  have h := left_oddCore_fixed_card_formula t
  rw [left_oddCore_fixed_intersection_card t] at h
  omega

theorem left_oddCore_card_le_intersection_cube (t : CubicTorus c) :
    Nat.card (cubicOddCore c t.x) ≤
      3*Nat.card (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G)^3 := by
  let D := cubicOddCore c t.x
  let W := cubicCoreLine c t.x
  let β := cubicOppositeQuotientAction c t.x t.y
  let : IsElementaryAbelian 3 (D ⧸ W) := t.left_oddCore_quotient_elementary
  have hb : β^3=1 := by
    rw [←map_pow,show t.y^3=1 from t.y_order ▸ pow_orderOf_eq_one t.y,map_one]
  have hh := MulAut.ternary_cubic_fixed_card_bound β hb
  rw [left_oddCore_quotient_fixed_card t] at hh
  have hc := t.left_oddCore_quotient_card
  rw [←hc,mul_comm]
  exact Nat.mul_le_mul_left 3 hh

theorem right_oddCore_twentySeven_of_left (t : CubicTorus c)
    (hcard : Nat.card (cubicOddCore c t.x)=27) :
    Nat.card (cubicOddCore (swapFactors c) t.y)=27 := by
  have hsmall : Nat.card (cubicOddCore (swapFactors c) t.y)≠3 := by
    intro h
    have hh := t.oddCore_three_iff.mpr h
    omega
  rcases t.right_oddCore_orders.resolve_left hsmall with h|h
  · exact h
  · have hi := oddCore_intersection_card_of_twentySeven t hcard
    have hh := left_oddCore_card_le_intersection_cube t.swap
    change Nat.card (cubicOddCore (swapFactors c) t.y) ≤
      3*Nat.card (cubicOddCore (swapFactors c) t.y ⊓ cubicOddCore c t.x : Subgroup G)^3 at hh
    rw [inf_comm,hi,h] at hh
    norm_num at hh

theorem oddCore_card_eq (t : CubicTorus c) :
    Nat.card (cubicOddCore c t.x)=Nat.card (cubicOddCore (swapFactors c) t.y) := by
  rcases t.left_oddCore_orders with h|h|h
  · rw [h,t.oddCore_three_iff.mp h]
  · rw [h,right_oddCore_twentySeven_of_left t h]
  · rcases t.right_oddCore_orders with k|k|k
    · have hh := t.oddCore_three_iff.mpr k; omega
    · have hh := right_oddCore_twentySeven_of_left t.swap k; change Nat.card (cubicOddCore c t.x)=27 at hh; omega
    · exact h.trans k.symm

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
