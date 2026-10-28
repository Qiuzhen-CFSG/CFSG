module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.OddCoreIntersection
public import Theory.GroupAction.CubicDisplacementLine

/-!
# Displacement onto the common cubic-core line

Suppose the marked odd core D has order 27. Its opposite cubic y has
nine fixed points, so its displacement is fixed by y. The marked central
involution z inverts this displacement, which consequently lies in the
opposite odd core E by the literal decomposition C_G(y)=E H₁. Thus
[y,D] lies in D ∩ E. The displacement map has kernel of order nine and
image the whole intersection of order three. In particular every yk,
k in D ∩ E, is conjugate to y by an element of D.

Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417; the centralizer and
inversion inputs are the q=3 instances of Fong–Wong §3B. This uses the
actual marked cores and does not use the q>3 line selection of Fong §6C.
The consumer `PairedCoreSylow` applies this to exclude Sylow order 81.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
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

private theorem left_displacement_fixed (t : CubicTorus c)
    (hcard : Nat.card (cubicOddCore c t.x)=27) (d : cubicOddCore c t.x) :
    cubicOppositeAction c t.x t.y (cubicOppositeAction c t.x t.y d*d⁻¹)=
      cubicOppositeAction c t.x t.y d*d⁻¹ := by
  let D := cubicOddCore c t.x
  let b := cubicOppositeAction c t.x t.y
  let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hcard
  have hb3 : b^3=1 := by
    rw [←map_pow,show t.y^3=1 from t.y_order ▸ pow_orderOf_eq_one t.y,map_one]
  have hfixed : Nat.card b.fixedSubgroup=9 := by
    let F := D ⊓ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G)
    have he : b.fixedSubgroup.map D.subtype=F := by
      ext a
      constructor
      · rintro ⟨v,hv,rfl⟩
        refine ⟨v.property,?_⟩
        rw [zpowers_eq_closure,centralizer_closure]
        have hh := congrArg Subtype.val ((MulAut.mem_fixedSubgroup b v).mp hv)
        exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
      · intro ha
        change a ∈ D ∧ a ∈ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G) at ha
        refine ⟨⟨a,ha.1⟩,?_,rfl⟩
        apply (MulAut.mem_fixedSubgroup b _).mpr
        apply Subtype.ext
        change ((t.y:c.H):G)*a*(((t.y:c.H):G))⁻¹=a
        have h := ha.2
        rw [zpowers_eq_closure,centralizer_closure] at h
        rw [←mem_centralizer_singleton_iff.mp h,mul_inv_cancel_right]
    rw [←card_map_of_injective D.subtype_injective,he]
    exact t.left_oddCore_twentySeven_fixed_card hcard
  exact MulAut.cubic_displacement_fixed_of_card_twentySeven b hb3 hcard hfixed d

theorem left_displacement_mem_intersection (t : CubicTorus c)
    (hcard : Nat.card (cubicOddCore c t.x)=27) (d : cubicOddCore c t.x) :
    ((t.y:c.H):G)*(d:G)*(((t.y:c.H):G))⁻¹*(d:G)⁻¹ ∈
      cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let b := cubicOppositeAction c t.x t.y
  let z : c.H₂ := ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
  let a := cubicOppositeAction c t.x z
  let δ : D := b d*d⁻¹
  have hfixed : ((δ:D):G) ∈ cubicCentralizer (swapFactors c) t.y := by
    apply mem_centralizer_singleton_iff.mpr
    exact (mul_inv_eq_iff_eq_mul.mp
      (congrArg Subtype.val (t.left_displacement_fixed hcard d))).symm
  have hE := fixed_displacement_mem_opposite t δ hfixed
  have hab : a*b=b*a := by
    rw [←map_mul,←map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.y.val.property)).symm
  have had : a d*d ∈ cubicCoreLine c t.x :=
    (cubic_oddCore_inversion c t.x t.x_order t.z
      ((orderOf_coe t.z).trans t.z_order) t.centralizer).1 d d.property
  have hnorm : b (a d*d)=a d*d := by
    apply Subtype.ext
    have hh : ((a d*d:D):G) ∈ zpowers ((t.x:c.H):G) := had
    have hyC : ((t.y:c.H):G) ∈ Subgroup.centralizer (zpowers ((t.x:c.H):G):Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
      exact opposite_factor_le_cubic_centralizer c t.x (mem_map_of_mem c.H.subtype t.y.property)
    change ((t.y:c.H):G)*((a d*d:D):G)*(((t.y:c.H):G))⁻¹=((a d*d:D):G)
    rw [←hyC _ hh,mul_inv_cancel_right]
  have hinv : a δ=δ⁻¹ := by
    let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hcard
    have hc : a (b d)=b (a d) := DFunLike.congr_fun hab d
    change a (b d*d⁻¹)=(b d*d⁻¹)⁻¹
    rw [map_mul,map_inv,hc]
    rw [map_mul] at hnorm
    have he : b (a d)=a d*d*(b d)⁻¹ := eq_mul_inv_of_mul_eq hnorm
    rw [he]
    simp only [mul_inv_rev,inv_inv]
    calc
      _ = a d*(d*(b d)⁻¹)*(a d)⁻¹ := by group
      _ = _ := by rw [mul_comm' (a d),mul_inv_cancel_right]
  have hδ3 : δ^3=1 := t.left_oddCore_cube δ
  have hδ : δ⁻¹*δ⁻¹=δ := by
    apply inv_injective
    simp only [mul_inv_rev,inv_inv]
    apply mul_eq_one_iff_eq_inv.mp
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hδ3
  have he : (t.z:G)*(δ:G)*(t.z:G)⁻¹*(δ:G)⁻¹=(δ:G) := by
    change ((a δ*δ⁻¹:D):G)=(δ:G)
    rw [hinv,hδ]
  rw [he] at hE
  exact ⟨δ.property,hE⟩

theorem left_intersection_conjugate (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27)
    (k : G) (hk : k ∈ cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y) :
    ∃ d : G, d ∈ cubicOddCore c t.x ∧
      MulAut.conj d ((t.y:c.H):G)=((t.y:c.H):G)*k := by
  let D := cubicOddCore c t.x
  let K := D ⊓ cubicOddCore (swapFactors c) t.y
  let b := cubicOppositeAction c t.x t.y
  let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hc
  let f : D →* K := {
    toFun d := ⟨((b d*d⁻¹:D):G),t.left_displacement_mem_intersection hc d⟩
    map_one' := by apply Subtype.ext; simp only [map_one,inv_one,mul_one]; rfl
    map_mul' d e := by
      apply Subtype.ext
      change ((b (d*e)*(d*e)⁻¹:D):G)=(((b d*d⁻¹)*(b e*e⁻¹):D):G)
      congr 1
      rw [map_mul,mul_inv_rev]
      calc
        _ = b d*(b e*e⁻¹)*d⁻¹ := by group
        _ = _ := by
          rw [mul_assoc, mul_comm' (b e*e⁻¹) (d⁻¹), ←mul_assoc] }
  have hker : f.ker.map D.subtype=D ⊓ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G) := by
    ext d
    constructor
    · rintro ⟨v,hv,rfl⟩
      refine ⟨v.property,?_⟩
      rw [zpowers_eq_closure,centralizer_closure]
      have hh : ((t.y:c.H):G)*(v:G)*(((t.y:c.H):G))⁻¹*(v:G)⁻¹=1 :=
        congrArg Subtype.val hv
      exact mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hh)).symm
    · intro hd
      refine ⟨⟨d,hd.1⟩,?_,rfl⟩
      apply Subtype.ext
      change ((t.y:c.H):G)*d*(((t.y:c.H):G))⁻¹*d⁻¹=1
      have hh := hd.2
      rw [zpowers_eq_closure,centralizer_closure] at hh
      rw [←mem_centralizer_singleton_iff.mp hh,mul_inv_cancel_right,mul_inv_cancel]
  have hkc : Nat.card f.ker=9 := by
    rw [←card_map_of_injective D.subtype_injective,hker]
    exact t.left_oddCore_twentySeven_fixed_card hc
  have hrc : Nat.card f.range=3 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hkc,hc] at hh
    omega
  have htop : f.range=⊤ := (card_eq_iff_eq_top _).mp
    (hrc.trans (t.oddCore_intersection_card_of_twentySeven hc).symm)
  obtain ⟨d,hd⟩ := MonoidHom.range_eq_top.mp htop ⟨k,hk⟩
  have hδ : ((t.y:c.H):G)*(d:G)*(((t.y:c.H):G))⁻¹*(d:G)⁻¹=k := congrArg Subtype.val hd
  have hdk : (d:G)*k=k*(d:G) := congrArg Subtype.val
    (mul_comm' d (⟨k,hk.1⟩:D))
  have hyk : ((t.y:c.H):G)*k=k*((t.y:c.H):G) := by
    have hh := (map_subtype_le (pPrimeCore 2 (cubicCentralizer (swapFactors c) t.y))) hk.2
    exact (mem_centralizer_singleton_iff.mp hh).symm
  refine ⟨(d:G)⁻¹,D.inv_mem d.property,?_⟩
  change (d:G)⁻¹*((t.y:c.H):G)*((d:G)⁻¹)⁻¹=((t.y:c.H):G)*k
  calc
    _ = (d:G)⁻¹*k*(d:G)*((t.y:c.H):G) := by rw [←hδ]; group
    _ = k*((t.y:c.H):G) := by
      rw [(show Commute (d:G) k from hdk).inv_left.eq]
      group
    _ = _ := hyk.symm

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
