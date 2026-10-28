module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PairedCoreSylow
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.TorusFusion

/-!
# The common cubic-core line has a large centralizer and diagonal fusion

Suppose both marked odd cores have order27, and put K=D∩E. The two
nonconjugate order81 extensions D⟨y⟩ and E⟨x⟩ both centralize K.
Sylow conjugacy inside the literal C_G(K) therefore forces 3^5 to divide
its order. Since each marked factor cubic has centralizer order27·24,
K cannot be conjugate to either factor line.

The original four-group normalizes K. Its action on this order-three
line has a nontrivial kernel, supplying an actual torus involution in
C_G(K). Ambient involution fusion moves K into H; Sylow conjugacy inside
H then moves it into the original cubic plane. The preceding exclusions
make this image a diagonal line. Its identification with the particular
M-diagonal is not asserted.

Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417. These deductions
continue the exceptional q=3 analysis; Fong, Nagoya Math. J.39 (1970),
§6, pp.74–76, instead invokes Janko for q=3, and §6C's line selection
uses q>3. The order27-core exclusion and the Sylow-nine branch still
require proofs, as does the Atlas recognition equivalence.
`Chapter14PairedCoreCentralizer` applies these conclusions to the literal
SourceLocalData consumer without a separate centralizer or fusion premise.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}

private theorem fifth_power_dvd_of_nonconjugate
    (R S C : Subgroup G) (hR : Nat.card R=81) (hS : Nat.card S=81)
    (hRC : R≤C) (hSC : S≤C)
    (hne : ∀ g : G, R.map (MulAut.conj g).toMonoidHom ≠ S) :
    3^5 ∣ Nat.card C := by
  by_contra hnot
  have hc (A : Subgroup G) (hA : Nat.card A=81) (hAC : A≤C) :
      Nat.card (A.subgroupOf C)=81 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv).trans hA
  have hi (A : Subgroup C) (hA : Nat.card A=81) : ¬3∣A.index := by
    intro hd
    apply hnot
    have hh := Nat.mul_dvd_mul_left 81 hd
    rw [←hA,A.card_mul_index,hA] at hh
    exact hh
  let P : Sylow 3 C := (IsPGroup.of_card (p:=3) (n:=4) (hc R hR hRC)).toSylow
    (hi (R.subgroupOf C) (hc R hR hRC))
  let Q : Sylow 3 C := (IsPGroup.of_card (p:=3) (n:=4) (hc S hS hSC)).toSylow
    (hi (S.subgroupOf C) (hc S hS hSC))
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq C P Q
  have he : (R.subgroupOf C).map (MulAut.conj g).toMonoidHom=S.subgroupOf C :=
    congrArg Sylow.toSubgroup hg
  apply hne g
  have hm := congrArg (fun A : Subgroup C => A.map C.subtype) he
  rw [map_subgroupOf_eq_of_le hSC] at hm
  calc
    R.map (MulAut.conj (g:G)).toMonoidHom =
        ((R.subgroupOf C).map C.subtype).map (MulAut.conj (g:G)).toMonoidHom := by
      rw [map_subgroupOf_eq_of_le hRC]
    _ = ((R.subgroupOf C).map (MulAut.conj g).toMonoidHom).map C.subtype := by
      rw [map_map,map_map]
      rfl
    _ = S := hm

namespace CubicTorus

theorem left_core_extension_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    Nat.card (cubicOddCore c t.x ⊔ zpowers ((t.y:c.H):G) : Subgroup G)=81 := by
  let D := cubicOddCore c t.x
  let Y := zpowers ((t.y:c.H):G)
  have hYL : Y ≤ c.H₂.map c.H.subtype := zpowers_le.mpr
    (mem_map_of_mem c.H.subtype t.y.property)
  have hYN : Y ≤ normalizer (D:Set G) :=
    (hYL.trans (opposite_factor_le_cubic_centralizer c t.x)).trans
      ((cubicCentralizer c t.x).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _)))
  have hd : Disjoint D Y := disjoint_iff.mpr (bot_unique
    ((inf_le_inf_left D hYL).trans (cubic_oddCore_inf_factor c t.x).le))
  rw [card_sup_eq_mul_of_normalizes_of_disjoint D Y hYN hd,hc,
    Nat.card_zpowers,orderOf_coe,orderOf_coe,t.y_order]

theorem core_intersection_centralizer_fifth_power_dvd (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    3^5 ∣ Nat.card (Subgroup.centralizer
      (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Set G)) := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let K := D ⊓ E
  let C := Subgroup.centralizer (K:Set G)
  let R := D ⊔ zpowers ((t.y:c.H):G)
  let S := E ⊔ zpowers ((t.x:c.H):G)
  have he := t.right_oddCore_twentySeven_of_left hc
  let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hc
  let : IsElementaryAbelian 3 E := t.right_oddCore_twentySeven_elementary he
  have hDC : D≤C := D.le_centralizer.trans (centralizer_le inf_le_left)
  have hEC : E≤C := E.le_centralizer.trans (centralizer_le inf_le_right)
  have hXC : zpowers ((t.x:c.H):G) ≤ C :=
    (cubic_line_le_oddCore c t.x t.x_order).trans hDC
  have hYC : zpowers ((t.y:c.H):G) ≤ C :=
    (cubic_line_le_oddCore (swapFactors c) t.y t.y_order).trans hEC
  exact fifth_power_dvd_of_nonconjugate R S C (t.left_core_extension_card hc)
    (t.swap.left_core_extension_card he) (sup_le hDC hYC) (sup_le hEC hXC)
    (t.core_extensions_not_conjugate hc)

theorem core_intersection_not_conjugate_left (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) (g : G) :
    (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y).map
      (MulAut.conj g).toMonoidHom ≠ zpowers ((t.x:c.H):G) := by
  intro he
  have hd := t.core_intersection_centralizer_fifth_power_dvd hc
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  have hmap := map_centralizer_le_centralizer_image (K:Set G) (MulAut.conj g).toMonoidHom
  change (Subgroup.centralizer (K:Set G)).map (MulAut.conj g).toMonoidHom ≤
    Subgroup.centralizer (K.map (MulAut.conj g).toMonoidHom:Set G) at hmap
  rw [he,zpowers_eq_closure,centralizer_closure] at hmap
  have hv := card_dvd_of_le hmap
  rw [card_map_of_injective (MulAut.conj g).injective] at hv
  have hh := hd.trans hv
  change 3^5 ∣ Nat.card (cubicCentralizer c t.x) at hh
  rw [cubic_centralizer_card c t.x t.x_order,hc] at hh
  norm_num at hh

theorem core_intersection_not_conjugate_right (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) (g : G) :
    (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y).map
      (MulAut.conj g).toMonoidHom ≠ zpowers ((t.y:c.H):G) := by
  have hh := t.swap.core_intersection_not_conjugate_left
    (t.right_oddCore_twentySeven_of_left hc) g
  change (cubicOddCore (swapFactors c) t.y ⊓ cubicOddCore c t.x).map
    (MulAut.conj g).toMonoidHom ≠ zpowers ((t.y:c.H):G) at hh
  simpa only [inf_comm] using hh

omit [Finite G] in
private theorem cubicNormalizer_le_core_normalizer (d : G2ThreeConfiguration G) (x : d.H₁) :
    cubicNormalizer d x ≤ normalizer (cubicOddCore d x:Set G) := by
  have hh := normalizer_le_normalizer_centralizer (zpowers ((x:d.H):G))
  have he : Subgroup.centralizer (zpowers ((x:d.H):G):Set G)=cubicCentralizer d x := by
    rw [zpowers_eq_closure,centralizer_closure]
    rfl
  rw [he] at hh
  exact hh.trans (normalizer_le_normalizer_characteristic_image
    (cubicCentralizer d x) (pPrimeCore 2 (cubicCentralizer d x)))

theorem torus_normalizes_core_intersection (t : CubicTorus c) :
    t.torus.map c.H.subtype ≤ normalizer
      ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G) := by
  have hx : t.torus.map c.H.subtype ≤ cubicNormalizer c t.x := by
    rw [t.left_ambient_normalizer]; exact le_sup_right
  have hy : t.torus.map c.H.subtype ≤ cubicNormalizer (swapFactors c) t.y := by
    rw [t.right_ambient_normalizer]; exact le_sup_right
  exact (le_inf (hx.trans (cubicNormalizer_le_core_normalizer c t.x))
    (hy.trans (cubicNormalizer_le_core_normalizer (swapFactors c) t.y))).trans
      inf_normalizer_le_normalizer_inf

theorem core_intersection_centralizing_involution (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    ∃ v : G, v ∈ t.torus.map c.H.subtype ∧ orderOf v=2 ∧
      v ∈ Subgroup.centralizer
        ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G) := by
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  let A := t.torus.map c.H.subtype
  let : IsKleinFour A := t.ambient_torus_kleinFour
  let : IsCyclic K := isCyclic_of_prime_card (t.oddCore_intersection_card_of_twentySeven hc)
  let f : A →* MulAut K := K.normalizerMonoidHom.comp
    (inclusion t.torus_normalizes_core_intersection)
  have hAut : Nat.card (MulAut K)=2 := by
    rw [IsCyclic.card_mulAut,t.oddCore_intersection_card_of_twentySeven hc]
    decide
  have hr : Nat.card f.range ∣ 2 := hAut ▸ f.range.card_subgroup_dvd_card
  have hprod := f.ker.card_mul_index
  rw [index_ker,show Nat.card A=4 from IsKleinFour.card_four] at hprod
  have hk : 2 ∣ Nat.card f.ker := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hr with h|h <;> rw [h] at hprod
    · have he : Nat.card f.ker=4 := by omega
      rw [he]; decide
    · have he : Nat.card f.ker=2 := by omega
      rw [he]
  obtain ⟨w,hw⟩ := exists_prime_orderOf_dvd_card' (G:=f.ker) 2 hk
  refine ⟨((w:A):G),w.val.property,?_,?_⟩
  · rw [orderOf_coe,orderOf_coe,hw]
  · intro k hk
    have he := DFunLike.congr_fun (show f (w:A)=1 from w.property) (⟨k,hk⟩:K)
    have hh : ((w:A):G)*k*(((w:A):G))⁻¹=k := congrArg Subtype.val he
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem exists_core_intersection_diagonal (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
    ∃ g : G,
      K.map (MulAut.conj g).toMonoidHom ≤
        zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) ∧
      K.map (MulAut.conj g).toMonoidHom ≠ zpowers ((t.x:c.H):G) ∧
      K.map (MulAut.conj g).toMonoidHom ≠ zpowers ((t.y:c.H):G) := by
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  obtain ⟨k,hk⟩ := exists_prime_orderOf_dvd_card' (G:=K) 3
    (by rw [t.oddCore_intersection_card_of_twentySeven hc])
  have hkg : orderOf (k:G)=3 := (orderOf_coe k).trans hk
  have hgen : zpowers (k:G)=K := eq_of_le_of_card_ge (zpowers_le.mpr k.property)
    (by rw [Nat.card_zpowers,hkg,t.oddCore_intersection_card_of_twentySeven hc])
  obtain ⟨v,_,hv,hvK⟩ := t.core_intersection_centralizing_involution hc
  obtain ⟨g,hg⟩ := isConj_iff.mp (involutions_conjugate c v t.z hv
    ((orderOf_coe t.z).trans t.z_order))
  change MulAut.conj g v=(t.z:G) at hg
  let a : G := MulAut.conj g k
  have haH : a ∈ c.H := by
    rw [t.centralizer]
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj g) (hvK k k.property)
    simpa only [map_mul,hg] using hh
  let aH : c.H := ⟨a,haH⟩
  have ha3 : orderOf aH=3 := (orderOf_coe aH).symm.trans
    (((MulAut.conj g).orderOf_eq k).trans hkg)
  let B : Subgroup c.H := zpowers (t.x:c.H) ⊔ zpowers (t.y:c.H)
  have hmap : B.map c.H.subtype=zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  have hB : Nat.card B=9 := by
    rw [←card_map_of_injective c.H.subtype_injective,hmap]
    exact (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  have hi : B.index=64 := by
    have hh := B.card_mul_index
    rw [hB,H_card c] at hh
    omega
  let P : Sylow 3 c.H := (IsPGroup.of_card (p:=3) (n:=2) hB).toSylow
    (by rw [hi]; decide)
  obtain ⟨b,hb⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n:=1) (by simpa using ha3)
  obtain ⟨h,hh⟩ := isConj_iff.mp hb
  let u : G := (h:G)*g
  have hu : MulAut.conj u (k:G)=((b:c.H):G) := by
    calc
      _ = (h:G)*(g*(k:G)*g⁻¹)*(h:G)⁻¹ := by dsimp [u]; group
      _ = _ := congrArg Subtype.val hh
  refine ⟨u,?_,t.core_intersection_not_conjugate_left hc u,
    t.core_intersection_not_conjugate_right hc u⟩
  change K.map (MulAut.conj u).toMonoidHom ≤ _
  rw [←hgen,MonoidHom.map_zpowers]
  apply zpowers_le.mpr
  change MulAut.conj u (k:G) ∈ _
  rw [hu,←hmap]
  exact mem_map_of_mem c.H.subtype b.property

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
