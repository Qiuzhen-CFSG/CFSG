module

public import Theory.GroupTheory.NormalFourCentralizer
public import Mathlib.GroupTheory.Sylow

/-!
# Disjoint commuting conjugates of a fused normal four

Let `E` be a normal four in a Sylow two-subgroup and `z` a central element.
Suppose every nonidentity element of `E` is conjugate to `z`, and a returning
conjugate containing `z` equals `E`. Then distinct returning conjugates of
`E` are disjoint and commute.

Transport a two-subgroup centralizing a conjugate of `z` into the Sylow
inside the centralizer of `z`. This identifies any transported four
containing `z`. A common nonidentity element consequently forces two fours
to coincide. Finally a four has a nontrivial intersection with the
index-at-most-two centralizer of `E`; transporting at such an element shows
mutual normalization. Disjointness then makes their commutator trivial.

This is the final geometric step of Janko–Thompson, Math. Z. 113 (1970),
§6, p.395. Fusion and returning-conjugate control are explicit hypotheses;
no classification or elementary rank bound is used.
-/

open Subgroup

namespace Sylow

/-- Transport a two-subgroup of an element centralizer while carrying
its distinguished element to a central Sylow element. -/
public theorem transport_centralizing_two_subgroup
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (z : S) (hzC : z ∈ center S) (x : G)
    (hc : IsConj x (z : G)) (R : Subgroup G) (hR : IsPGroup 2 R)
    (hRC : R ≤ centralizer ({x} : Set G)) :
    ∃ k : G, R.map (MulAut.conj k).toMonoidHom ≤ (S : Subgroup G) ∧
      (MulAut.conj k) x = z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  let C := centralizer ({(z : G)} : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hzC ⟨s, hs⟩))
  let K := R.map (MulAut.conj g).toMonoidHom
  have hKC : K ≤ C := by
    rintro y ⟨r, hr, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (hRC hr))
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, show (MulAut.conj g) x = z from hg] using h
  have hp : IsPGroup 2 (K.subgroupOf C) := (hR.map _).comap_subtype
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq C T (S.subtype hSC)
  have htrans : (K.subgroupOf C).map (MulAut.conj n).toMonoidHom ≤
      (S.subtype hSC : Subgroup C) := by
    rw [← hn]
    exact map_mono hT
  refine ⟨(n : G) * g, ?_, ?_⟩
  · rintro y ⟨r, hr, rfl⟩
    have hk : (MulAut.conj g) r ∈ K := mem_map_of_mem _ hr
    have h := htrans (mem_map_of_mem (MulAut.conj n).toMonoidHom
      (show (⟨(MulAut.conj g) r, hKC hk⟩ : C) ∈ K.subgroupOf C from hk))
    change (n : G) * ((MulAut.conj g) r) * (n : G)⁻¹ ∈ (S : Subgroup G) at h
    simpa [MulAut.conj_apply, mul_assoc] using h
  · have hnz := mem_centralizer_singleton_iff.mp n.property
    calc
      (MulAut.conj ((n : G) * g)) x = (MulAut.conj (n : G)) ((MulAut.conj g) x) := by
        simp [MulAut.conj_apply, mul_assoc]
      _ = (MulAut.conj (n : G)) (z : G) := congrArg _ hg
      _ = z := mul_inv_eq_iff_eq_mul.mpr hnz

private theorem conj_map_comp {G : Type*} [Group G] (W : Subgroup G) (g k : G) :
    (W.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      W.map (MulAut.conj (k * g)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

variable {G : Type*} [Group G] [Finite G]
variable (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
variable (z : S) (hzC : z ∈ center S)
variable (hreturn : ∀ g : G,
  (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
  (z : G) ∈ (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom →
  (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom = E.map (S : Subgroup G).subtype)
variable (hfused : ∀ x : S, x ∈ E → x ≠ 1 → IsConj (x : G) (z : G))

include hfused in
omit [Finite G] [E.Normal] [IsElementaryAbelian 2 E] in
private theorem fusion_conjugate_to_center (g : G) (x : G)
    (hx : x ∈ (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom)
    (hx1 : x ≠ 1) : IsConj x (z : G) := by
  obtain ⟨y, ⟨e, he, rfl⟩, rfl⟩ := hx
  have he1 : e ≠ 1 := by rintro rfl; exact hx1 (map_one _)
  exact (isConj_iff.mpr ⟨g, rfl⟩ : IsConj (e : G) ((MulAut.conj g) (e : G))).symm.trans
    (hfused e he he1)

include hzC hreturn hfused in
omit [IsElementaryAbelian 2 E] in
/-- A two-overgroup centralizing a nonidentity element of a fused conjugate
normalizes that conjugate, provided returning fours through `z` are fixed. -/
public theorem conjugate_normalized_by_centralizing_two_overgroup
    (g : G) (R : Subgroup G) (hR : IsPGroup 2 R)
    (hVR : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤ R)
    (x : G) (hx : x ∈ (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom)
    (hx1 : x ≠ 1) (hRC : R ≤ centralizer ({x} : Set G)) :
    R ≤ normalizer (((E.map (S : Subgroup G).subtype).map
      (MulAut.conj g).toMonoidHom) : Set G) := by
  let W := E.map (S : Subgroup G).subtype
  let V := W.map (MulAut.conj g).toMonoidHom
  obtain ⟨k, hkS, hkx⟩ := transport_centralizing_two_subgroup S z hzC x
    (fusion_conjugate_to_center S E z hfused g x hx hx1) R hR hRC
  have hVk : V.map (MulAut.conj k).toMonoidHom = W := by
    rw [conj_map_comp]
    apply hreturn
    · rw [← conj_map_comp]
      exact (map_mono hVR).trans hkS
    · rw [← conj_map_comp, ← hkx]
      exact mem_map_of_mem _ hx
  have hWN : (S : Subgroup G) ≤ normalizer (W : Set G) := by
    simpa only [E.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      E.le_normalizer_map (S : Subgroup G).subtype
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply map_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
  change (V.map (MulAut.conj r).toMonoidHom).map (MulAut.conj k).toMonoidHom =
    V.map (MulAut.conj k).toMonoidHom
  have hswitch : (V.map (MulAut.conj r).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      (V.map (MulAut.conj k).toMonoidHom).map
        (MulAut.conj ((MulAut.conj k) r)).toMonoidHom := by
    rw [conj_map_comp V r k, conj_map_comp V k ((MulAut.conj k) r)]
    have he : k * r = (MulAut.conj k) r * k := by simp [MulAut.conj_apply, mul_assoc]
    rw [he]
  rw [hswitch, hVk]
  exact mem_normalizer_iff_map_conj_eq.mp (hWN (hkS (mem_map_of_mem _ hr)))

include hzC hreturn hfused in
omit [E.Normal] in
/-- Distinct returning conjugates of a fused four have trivial intersection. -/
public theorem disjoint_conjugate_of_fusion_control (g : G)
    (hVS : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G))
    (hne : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠ E.map (S : Subgroup G).subtype) :
    Disjoint (E.map (S : Subgroup G).subtype)
      ((E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) := by
  let W := E.map (S : Subgroup G).subtype
  let V := W.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro x hx
  change x = 1
  by_contra hx1
  have hRS : W ⊔ V ≤ (S : Subgroup G) := sup_le (map_subtype_le E) hVS
  have hRp : IsPGroup 2 (W ⊔ V : Subgroup G) := (S.isPGroup'.to_subgroup ((W ⊔ V).subgroupOf (S : Subgroup G))).of_equiv (subgroupOfEquivOfLe hRS)
  have hRC : W ⊔ V ≤ centralizer ({x} : Set G) := by
    apply sup_le
    · intro w hw
      exact mem_centralizer_singleton_iff.mpr (W.le_centralizer hw x hx.1).symm
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (V.le_centralizer hv x hx.2).symm
  obtain ⟨k, hkS, hkx⟩ := transport_centralizing_two_subgroup S z hzC x
    (fusion_conjugate_to_center S E z hfused g x hx.2 hx1) (W ⊔ V) hRp hRC
  have hWk : W.map (MulAut.conj k).toMonoidHom = W := hreturn k
    ((map_mono le_sup_left).trans hkS) (hkx ▸ mem_map_of_mem _ hx.1)
  have hVk : V.map (MulAut.conj k).toMonoidHom = W := by
    rw [conj_map_comp]
    apply hreturn
    · rw [← conj_map_comp]
      exact (map_mono le_sup_right).trans hkS
    · rw [← conj_map_comp, ← hkx]
      exact mem_map_of_mem _ hx.2
  exact hne (map_injective (MulAut.conj k).injective (hVk.trans hWk.symm))

include hzC hreturn hfused in
/-- A distinct returning conjugate of the fused normal four is disjoint
from it and centralizes it. -/
public theorem disjoint_commuting_conjugate_of_fusion_control (hE : Nat.card E = 4) (g : G)
    (hVS : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G))
    (hne : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠ E.map (S : Subgroup G).subtype) :
    Disjoint (E.map (S : Subgroup G).subtype)
      ((E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) ∧
    (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (E.map (S : Subgroup G).subtype : Set G) := by
  let W := E.map (S : Subgroup G).subtype
  let V := W.map (MulAut.conj g).toMonoidHom
  let VS := V.subgroupOf (S : Subgroup G)
  let C := centralizer (E : Set S)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hd : Disjoint W V := disjoint_conjugate_of_fusion_control S E z hzC hreturn hfused g hVS hne
  refine ⟨hd, ?_⟩
  have hVC : Nat.card VS = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVS).toEquiv,
      card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (S : Subgroup G).subtype_injective, hE]
  have hi : C.index ≤ 2 := centralizer_index_le_two_of_normal_four S.isPGroup' E hE
  have hri : (C.subgroupOf VS).index ≤ 2 := by
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero C.index_ne_zero_of_finite)
      (C.relIndex_dvd_index_of_normal VS)).trans hi
  have hc := (C.subgroupOf VS).card_mul_index
  rw [hVC] at hc
  have htwo : 1 < Nat.card (C.subgroupOf VS) := by nlinarith
  let : Nontrivial (C.subgroupOf VS) := Finite.one_lt_card_iff_nontrivial.mp htwo
  obtain ⟨a, ha⟩ := exists_ne (1 : C.subgroupOf VS)
  let x : G := (((a : VS) : S) : G)
  have hxV : x ∈ V := (a : VS).property
  have hx1 : x ≠ 1 := by
    intro h
    exact ha (Subtype.ext (Subtype.ext (Subtype.ext h)))
  have hxC : x ∈ centralizer (W : Set G) := by
    rintro w ⟨e, he, rfl⟩
    exact congrArg Subtype.val (a.property e he)
  have hRS : W ⊔ V ≤ (S : Subgroup G) := sup_le (map_subtype_le E) hVS
  have hp : IsPGroup 2 (W ⊔ V : Subgroup G) :=
    S.isPGroup'.of_injective (inclusion hRS) (inclusion_injective hRS)
  have hRC : W ⊔ V ≤ centralizer ({x} : Set G) := by
    apply sup_le
    · intro w hw
      exact mem_centralizer_singleton_iff.mpr (hxC w hw)
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (V.le_centralizer hv x hxV).symm
  have hWV : W ≤ normalizer (V : Set G) := le_sup_left.trans
    (conjugate_normalized_by_centralizing_two_overgroup S E z hzC hreturn hfused
      g (W ⊔ V) hp le_sup_right x hxV hx1 hRC)
  have hWN : (S : Subgroup G) ≤ normalizer (W : Set G) := by
    simpa only [E.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      E.le_normalizer_map (S : Subgroup G).subtype
  have hcomm : ⁅V, W⁆ ≤ V ⊓ W := le_inf
    (le_normalizer_iff_commutator_le_left.mp hWV)
    (le_normalizer_iff_commutator_le_right.mp (hVS.trans hWN))
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact le_bot_iff.mp ((disjoint_iff.mp hd.symm) ▸ hcomm)

end Sylow
