module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PairedCoreExclusion
public import Theory.GroupAction.SL23CubicFixedCard
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedProductCentralizer

/-!
# The common plane in the order-243-core branch

For the two original marked odd cores D and F of order243, the opposite
SL₂(3) action on D/⟨x⟩ has nine fixed points. The existing exact lifting
and displacement identities therefore give |D∩F|=9 and |C_D(y)|=27.
The intersection is elementary abelian. Coordinate uniqueness in the
literal split C_G(x)=D H₂ then computes the full plane centralizer.

Writing E=⟨x,y⟩, the subgroup U=E(D∩F) is elementary abelian of order81.
The full centralizer C_G(E)=U⟨z⟩ has order162 and O₃(C_G(E))=U. Also
C_G(U)=U: an involution centralizing U would place an order81 subgroup in
an involution centralizer of order576, which is impossible.

These are consequences of the original (G1)–(G2) markings in
Aschbacher–Smith I.4.5, printed p.417 (refs/quasithin.pdf, PDF p.428).
They continue the exceptional q=3 analysis using the marked centralizer
splittings of Fong–Wong §3B. They do not exclude the strongly-three-embedded
branch or construct the required Atlas equivalence. Chapter14MaximalCore
applies them to the actual SourceLocalData and retains the final recognition
obligation with its owner.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

theorem maximal_core_quotient_fixed_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (cubicOppositeQuotientAction c t.x t.y).fixedSubgroup=9 := by
  let D := cubicOddCore c t.x
  let W := cubicCoreLine c t.x
  let : IsElementaryAbelian 3 (D ⧸ W) := t.left_oddCore_quotient_elementary
  let z : c.H₂ := ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
  have hz : orderOf z=2 := (orderOf_coe z).symm.trans t.z_order
  have hq : Nat.card (D ⧸ W)=81 := by
    have hh := t.left_oddCore_quotient_card
    rw [hc] at hh
    change Nat.card (D ⧸ W)*3=243 at hh
    omega
  apply sl23_inverting_cubic_fixed_card_eightyOne c.H₂_model.some
    (cubicOppositeQuotientAction c t.x) t.y z t.y_order hz _ hq
  intro a
  obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective W a
  exact t.left_oddCore_quotient_inverted d

theorem maximal_core_intersection_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G)=9 := by
  rw [←t.left_oddCore_quotient_fixed_card,t.maximal_core_quotient_fixed_card hc]

theorem maximal_core_intersection_elementary (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    IsElementaryAbelian 3 (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G) := by
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  let : IsMulCommutative K := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p:=3) (t.maximal_core_intersection_card hc)
  refine {exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_}
  intro a
  apply Subtype.ext
  exact congrArg (fun v : cubicOddCore c t.x => (v:G)) (t.left_oddCore_cube ⟨a,a.property.1⟩)

theorem maximal_core_opposite_fixed_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (cubicOddCore c t.x ⊓ Subgroup.centralizer
      (zpowers ((t.y:c.H):G):Set G) : Subgroup G)=27 := by
  rw [t.left_oddCore_fixed_intersection_card,t.maximal_core_intersection_card hc]


omit [Finite G] in
private theorem left_core_normalized (t : CubicTorus c) :
    c.H₂.map c.H.subtype ≤ normalizer (cubicOddCore c t.x:Set G) :=
  (opposite_factor_le_cubic_centralizer c t.x).trans
    ((cubicCentralizer c t.x).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _)))

private theorem opposite_cubic_fixed (t : CubicTorus c) :
    c.H₂.map c.H.subtype ⊓ Subgroup.centralizer ({((t.y:c.H):G)}:Set G) =
      zpowers (t.z:G) ⊔ zpowers ((t.y:c.H):G) := by
  have he : ((Subgroup.centralizer ({t.y}:Set c.H₂)).map c.H₂.subtype).map c.H.subtype =
      c.H₂.map c.H.subtype ⊓ Subgroup.centralizer ({((t.y:c.H):G)}:Set G) := by
    ext g
    constructor
    · rintro ⟨h,⟨a,ha,rfl⟩,rfl⟩
      exact ⟨mem_map_of_mem c.H.subtype a.property,
        mem_centralizer_singleton_iff.mpr
          (congrArg (fun v : c.H₂ => ((v:c.H):G))
            (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨⟨h,hh,rfl⟩,hc⟩
      refine ⟨h,⟨⟨h,hh⟩,mem_centralizer_singleton_iff.mpr ?_,rfl⟩,rfl⟩
      exact Subtype.ext (Subtype.ext (mem_centralizer_singleton_iff.mp hc))
  rw [←he,Matrix.SpecialLinearGroup.cubic_centralizer_of_equiv c.H₂_model.some t.y t.y_order,
    Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
  have hz := left_factor_center (swapFactors c)
  change (center c.H₂).map c.H₂.subtype=c.H₂⊓c.H₁ at hz
  rw [hz,inf_comm,←t.central_line,MonoidHom.map_zpowers]
  rfl

/-- The centralizer is computed on the original cubic plane, with all markings retained. -/
theorem cubic_plane_centralizer (t : CubicTorus c) :
    Subgroup.centralizer ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G) =
      (zpowers ((t.x:c.H):G) ⊔
        (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)) ⊔
      (zpowers (t.z:G) ⊔ zpowers ((t.y:c.H):G)) := by
  let D := cubicOddCore c t.x
  let L := c.H₂.map c.H.subtype
  let y : G := ((t.y:c.H):G)
  have hyL : y∈L := mem_map_of_mem c.H.subtype t.y.property
  have he : Subgroup.centralizer ((zpowers ((t.x:c.H):G) ⊔ zpowers y : Subgroup G):Set G) =
      cubicCentralizer c t.x ⊓ Subgroup.centralizer ({y}:Set G) := by
    ext a
    constructor
    · intro ha
      exact ⟨mem_centralizer_singleton_iff.mpr (ha _ (mem_sup_left (mem_zpowers _))).symm,
        mem_centralizer_singleton_iff.mpr (ha _ (mem_sup_right (mem_zpowers _))).symm⟩
    · rintro ⟨hx,hy⟩
      have h1 : zpowers ((t.x:c.H):G)≤Subgroup.centralizer ({a}:Set G) :=
        zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hx).symm)
      have h2 : zpowers y≤Subgroup.centralizer ({a}:Set G) :=
        zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hy).symm)
      intro b hb
      exact mem_centralizer_singleton_iff.mp ((sup_le h1 h2) hb)
  rw [he,cubic_centralizer_split c t.x t.x_order]
  rw [sup_inf_centralizer_of_normalized_disjoint D L y t.left_core_normalized
    (disjoint_iff.mpr (cubic_oddCore_inf_factor c t.x))
    (t.left_core_normalized hyL) (L.le_normalizer hyL),t.opposite_cubic_fixed]
  have hh := t.left_oddCore_fixed_decomposition
  rw [zpowers_eq_closure,centralizer_closure] at hh
  rw [hh]

theorem maximal_plane_centralizer_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (Subgroup.centralizer
      ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G))=162 := by
  let D := cubicOddCore c t.x
  let L := c.H₂.map c.H.subtype
  let C := Subgroup.centralizer ({((t.y:c.H):G)}:Set G)
  have hDc : Nat.card (D⊓C : Subgroup G)=27 := by
    have hh := t.maximal_core_opposite_fixed_card hc
    rwa [zpowers_eq_closure,centralizer_closure] at hh
  have hLc : Nat.card (L⊓C : Subgroup G)=6 := by
    rw [t.opposite_cubic_fixed]
    have hzY : zpowers ((t.y:c.H):G)≤Subgroup.centralizer (zpowers (t.z:G):Set G) := by
      apply zpowers_le.mpr
      rw [zpowers_eq_closure,centralizer_closure,←t.centralizer]
      exact t.y.val.property
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hzY.trans (Subgroup.centralizer_le_normalizer _))
      (disjoint_of_coprime_natCard (by
        rw [Nat.card_zpowers,Nat.card_zpowers,orderOf_coe,orderOf_coe,orderOf_coe,
          t.z_order,t.y_order]; decide)),
      Nat.card_zpowers,Nat.card_zpowers,orderOf_coe,orderOf_coe,orderOf_coe,t.z_order,t.y_order]
  have hn : L⊓C≤normalizer (D⊓C : Set G) :=
    (le_inf (inf_le_left.trans t.left_core_normalized) (inf_le_right.trans C.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hd : Disjoint (D⊓C) (L⊓C) :=
    (disjoint_iff.mpr (cubic_oddCore_inf_factor c t.x)).mono inf_le_left inf_le_left
  have hsplit : Subgroup.centralizer
      ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G) =
      (D⊓C)⊔(L⊓C) := by
    rw [t.cubic_plane_centralizer,t.opposite_cubic_fixed]
    have hh := t.left_oddCore_fixed_decomposition
    rw [zpowers_eq_closure,centralizer_closure] at hh
    rw [hh]
  rw [hsplit,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd,hDc,hLc]


/-- The plane centralizer contains an elementary subgroup of order81 made from
its original plane and the actual common core. -/
theorem maximal_plane_elementary_extension (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
    let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
    IsElementaryAbelian 3 (E⊔K : Subgroup G) ∧ Nat.card (E⊔K : Subgroup G)=81 ∧
      Subgroup.centralizer (E:Set G)=(E⊔K)⊔zpowers (t.z:G) := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  have hEH : E≤c.H := sup_le (zpowers_le.mpr t.x.val.property)
    (zpowers_le.mpr t.y.val.property)
  have hKC : K≤Subgroup.centralizer (E:Set G) := by
    rw [t.cubic_plane_centralizer]
    exact le_trans le_sup_right le_sup_left
  have hd : Disjoint K E := by
    apply disjoint_iff.mpr
    apply bot_unique
    have hX : K⊓E≤zpowers ((t.x:c.H):G) :=
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hEH)).trans
        (cubic_oddCore_fixed c t.x t.x_order).le
    exact (le_inf (inf_le_left.trans inf_le_right)
      (hX.trans (zpowers_le.mpr (mem_map_of_mem c.H.subtype t.x.property)))).trans
      (cubic_oddCore_inf_factor (swapFactors c) t.y).le
  let : IsElementaryAbelian 3 E := (cubic_plane_data c t.x t.y t.x_order t.y_order).1
  let : IsElementaryAbelian 3 K := t.maximal_core_intersection_elementary hc
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hKC,?_,?_⟩
  · rw [card_sup_eq_mul_of_normalizes_of_disjoint E K
      (hKC.trans (Subgroup.centralizer_le_normalizer _)) hd.symm,
      (cubic_plane_data c t.x t.y t.x_order t.y_order).2,t.maximal_core_intersection_card hc]
  · rw [t.cubic_plane_centralizer]
    ac_rfl


/-- The order81 extension is the actual three-core of the full plane centralizer. -/
theorem maximal_plane_threeCore (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
    (Subgroup.centralizer (E:Set G)).pCoreIn 3 =
      E ⊔ (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y) := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  let U := E⊔K
  let C := Subgroup.centralizer (E:Set G)
  obtain ⟨hu,hUc,hC⟩ := t.maximal_plane_elementary_extension hc
  change C=U⊔zpowers (t.z:G) at hC
  change Nat.card U=81 at hUc
  let : IsElementaryAbelian 3 U := hu
  have hzE : (t.z:G)∈Subgroup.centralizer (E:Set G) := by
    intro a ha
    have hEH : E≤c.H := sup_le (zpowers_le.mpr t.x.val.property)
      (zpowers_le.mpr t.y.val.property)
    exact mem_centralizer_singleton_iff.mp (t.centralizer ▸ hEH ha)
  have hzK : (t.z:G)∈normalizer (K:Set G) := t.torus_normalizes_core_intersection
    (mem_map_of_mem c.H.subtype (mem_sup_left (mem_zpowers t.z)))
  have hzU : (t.z:G)∈normalizer (U:Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup E K
      ⟨Subgroup.centralizer_le_normalizer _ hzE,hzK⟩
  have hn : C≤normalizer (U:Set G) := by
    rw [hC]
    exact sup_le U.le_normalizer (zpowers_le.mpr hzU)
  have hUC : U≤C := by rw [hC]; exact le_sup_left
  have hle : U≤C.pCoreIn 3 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 3 U) hUC hn
  have ho : Nat.Coprime (Nat.card (C.pCoreIn 3)) 2 := by
    obtain ⟨n,he⟩ := (isPGroup_pCoreIn 3 C).exists_card_eq
    rw [he]
    exact (by decide : Nat.Coprime 3 2).pow_left n
  have hd : Nat.card (C.pCoreIn 3)∣81 := by
    have hh := card_dvd_of_le (pCoreIn_le 3 C)
    rw [t.maximal_plane_centralizer_card hc] at hh
    exact ho.dvd_of_dvd_mul_left hh
  exact (eq_of_le_of_card_ge hle (by
    rw [hUc]
    exact Nat.le_of_dvd (by decide) hd)).symm


/-- The same literal elementary81 is self-centralizing in the ambient group. -/
theorem maximal_plane_extension_selfCentralizing (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
    let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
    Subgroup.centralizer (U:Set G)=U := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
  let C := Subgroup.centralizer (U:Set G)
  obtain ⟨hu,hUc,_⟩ := t.maximal_plane_elementary_extension hc
  change Nat.card U=81 at hUc
  let : IsElementaryAbelian 3 U := hu
  have hodd : Odd (Nat.card C) := by
    apply Nat.not_even_iff_odd.mp
    intro heven
    obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G:=C) 2 (even_iff_two_dvd.mp heven)
    have hvG : orderOf (v:G)=2 := (orderOf_coe v).trans hv
    have hUV : U≤Subgroup.centralizer ({(v:G)}:Set G) := by
      intro u hu
      exact mem_centralizer_singleton_iff.mpr (v.property u hu)
    have hh := card_dvd_of_le hUV
    rw [hUc,involution_centralizer_card c v hvG] at hh
    norm_num at hh
  have hd : Nat.card C∣81 := by
    have hh := card_dvd_of_le (centralizer_le (show E≤U from le_sup_left))
    change Nat.card C∣Nat.card (Subgroup.centralizer (E:Set G)) at hh
    rw [t.maximal_plane_centralizer_card hc] at hh
    exact hodd.coprime_two_right.dvd_of_dvd_mul_left hh
  exact (eq_of_le_of_card_ge U.le_centralizer (by
    rw [hUc]
    exact Nat.le_of_dvd (by decide) hd)).symm

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
