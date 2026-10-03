module

public import Stellmacher.Recognition.Parrott.SecondCentralizerOuterSelection
public import Stellmacher.Recognition.Parrott.SecondCentralizerSylowGeometry

/-!
# Excluding the fixed involution from the compatible omega center

Every element of F centralizes at least 64 elements of the omega subgroup
of O₂(N_G(F)). For points outside its center, normalizer fusion reduces
this to a point in E∩F. Inside the original core of order 512, its
centralizer of order 256 meets the centralizer of the omega center,
of order 128, in at least 64 elements. The latter centralizer lies in omega.

For a compatible fixed join e.F=C_V(w), suppose the prescribed fixed
involution v belongs to its omega center. Its entire omega subgroup then
lies in C_H(v)=P≤V. Thus its centralizer of w lies in e.F, contradicting
the lower bound 64 and |e.F|=32. The equality identifying the fixed join
is supplied explicitly; no ambient centralizer containment is assumed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678 and §4, p.682.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem omega_centralizer_card_conj (W : Subgroup G) (n l : G)
    (hn : n ∈ normalizer (W : Set G)) :
    Nat.card (W ⊓ centralizer ({n * l * n⁻¹} : Set G) : Subgroup G) =
      Nat.card (W ⊓ centralizer ({l} : Set G) : Subgroup G) := by
  let f := MulAut.conj n
  have hm : (centralizer ({l} : Set G)).map f.toMonoidHom =
      centralizer ({f l} : Set G) := by
    apply le_antisymm
    · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
        map_centralizer_le_centralizer_image ({l} : Set G) f.toMonoidHom
    · intro y hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      simpa only [map_mul, f.apply_symm_apply] using
        mem_centralizer_singleton_iff.mp hy
  have hW : W.map f.toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp hn
  have he : (W ⊓ centralizer ({l} : Set G) : Subgroup G).map f.toMonoidHom =
      W ⊓ centralizer ({f l} : Set G) := by rw [map_inf _ _ _ f.injective, hm, hW]
  change Nat.card (W ⊓ centralizer ({f l} : Set G) : Subgroup G) = _
  rw [← he, card_map_of_injective f.injective]

/-- Every element of the elementary subgroup fixes at least 64 elements of
its normalizer's omega subgroup. -/
public theorem normalizer_omega_elementary_centralizer_lower_bound
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    ∀ l ∈ d.F, 64 ≤ Nat.card (W ⊓ centralizer ({l} : Set G) : Subgroup G) := by
  intro N K W l hl
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let L := J.map H.subtype
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let U := omega₁ K (p := 2)
  let i := N.subtype.comp K.subtype
  let Z := (center U).map (i.comp U.subtype)
  have hi : Function.Injective i := N.subtype_injective.comp K.subtype_injective
  have hWcard : Nat.card W = 256 :=
    (card_map_of_injective hi).trans (d.normalizer_core_omega_structure h hN hproper).1
  have hZcard : Nat.card Z = 8 :=
    (card_map_of_injective (f := i.comp U.subtype) (hi.comp U.subtype_injective)).trans
      (d.normalizer_core_omega_structure h hN hproper).2.1
  have hZE : Z ≤ E ⊓ d.F := (d.normalizer_core_omega_structure h hN hproper).2.2.1
  have hzZ : z ∈ Z := d.normalizer_core_omega_inclusions.2.1 d.z_mem_normalizer_core_center
  by_cases hlZ : l ∈ Z
  · have hWC : W ≤ W ⊓ centralizer ({l} : Set G) := by
      refine le_inf le_rfl ?_
      obtain ⟨lU, hlU, rfl⟩ := hlZ
      rintro x ⟨xK, hxK, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg (i.comp U.subtype) (mem_center_iff.mp hlU ⟨xK, hxK⟩))
    have hc := card_le_of_le hWC
    rw [hWcard] at hc
    omega
  have hnot : ¬ E ⊓ d.F ≤ Z := by
    intro hh
    have hc := card_le_of_le hh
    rw [d.inf_card, hZcard] at hc
    omega
  obtain ⟨u, hu, huZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hucard := d.normalizer_elementary_outside_omega_center_centralizer_card
    h hN hproper u hu huZ
  obtain ⟨n, hn⟩ := d.normalizer_elementary_outside_omega_center_fusion_of_centralizer_card
    h hN hproper u hu.2 huZ hucard l hl hlZ
  let B := L ⊓ centralizer (Z : Set G)
  let A := L ⊓ centralizer ({u} : Set G)
  have hB : Nat.card B = 128 := by
    have hc := parrott_core_inf_centralizer_card z h Z (zpowers_le.mpr hzZ)
      (hZE.trans inf_le_left)
    change Nat.card Z * Nat.card B = 1024 at hc
    rw [hZcard] at hc
    omega
  have hA : Nat.card A = 256 := by
    exact parrott_derived_core_centralizer_card z h u hu.1
      (fun hh => huZ ((zpowers_le.mpr hzZ) hh))
  have hL : Nat.card L = 512 :=
    (card_map_of_injective H.subtype_injective).trans h.core_card
  have hidx : A.relIndex L ≤ 2 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) A L bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, hL, hA] at hc
    omega
  have hnidx : A.relIndex L ≠ 0 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) A L bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, hL, hA] at hc
    omega
  have hiidx : (A ⊓ B).relIndex B ≤ 2 := by
    rw [inf_relIndex_right]
    exact (relIndex_le_of_le_right (show B ≤ L from inf_le_left) hnidx).trans hidx
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ B) B bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, hB] at hc
  have hb : 64 ≤ Nat.card (A ⊓ B : Subgroup G) := by nlinarith
  have hBW : B ≤ W := by
    have heq : N ⊓ centralizer (Z : Set G) = W :=
      d.normalizer_omega_center_centralizer h hN hproper
    rw [← heq]
    exact inf_le_inf_right _ (d.core_le_sylow.trans d.sylow_le_normalizer)
  have huBound : 64 ≤ Nat.card (W ⊓ centralizer ({u} : Set G) : Subgroup G) :=
    hb.trans (card_le_of_le (by
      intro x hx
      exact ⟨hBW hx.2, hx.1.2⟩))
  let V := U.map K.subtype
  let : U.Characteristic := omega₁_characteristic K
  let : V.Normal := ConjAct.normal_of_characteristic_of_normal
  have hNW : N ≤ normalizer (W : Set G) := by
    have hh := le_normalizer_map (H := V) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, V, W, map_map] using hh
  have he := omega_centralizer_card_conj W n u (hNW n.property)
  rw [hn] at he
  exact he.symm ▸ huBound

/-- The compatible fixed join's omega center cannot contain the prescribed
fixed involution. -/
public theorem normalizer_fixed_join_outside_omega_center
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let V := N ⊓ centralizer ({v} : Set G)
    ∀ (w : G) (e : ParrottSecondElementaryData z),
      (e.a : G) = w → e.F = V ⊓ centralizer ({w} : Set G) →
      (e.sylow : Subgroup G) < normalizer (e.F : Set G) →
      let M := normalizer (e.F : Set G)
      let Kₑ := pCore 2 M
      let Uₑ := omega₁ Kₑ (p := 2)
      v ∉ (center Uₑ).map ((M.subtype.comp Kₑ.subtype).comp Uₑ.subtype) := by
  intro N V w e hea heF heproper M Ke Ue hvZ
  let H := centralizer ({z} : Set G)
  let C := centralizer ({v} : Set G)
  let P := (d.sylow : Subgroup G) ⊓ C
  let i := M.subtype.comp Ke.subtype
  let We := Ue.map i
  let Ze := (center Ue).map (i.comp Ue.subtype)
  have hzZ : z ∈ Ze := e.normalizer_core_omega_inclusions.2.1 e.z_mem_normalizer_core_center
  have hWC (x : G) (hx : x ∈ Ze) : We ≤ centralizer ({x} : Set G) := by
    obtain ⟨xU, hxU, rfl⟩ := hx
    rintro y ⟨yK, hyK, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (i.comp Ue.subtype) (mem_center_iff.mp hxU ⟨yK, hyK⟩))
  have hPH : P ≤ H ⊓ C := inf_le_inf_right _ d.sylow_le_centralizer
  have hPc : Nat.card P = 512 := d.normalizer_fixed_sylow_card h hN hproper Q v hv hfix
  have hHC : H ⊓ C = P := (eq_of_le_of_card_ge hPH (by
    rw [hPc, d.supplied_fixed_original_centralizer_card h hN hproper Q v hv hfix])).symm
  have hWP : We ≤ P := hHC ▸ le_inf (hWC z hzZ) (hWC v hvZ)
  have hWV : We ≤ V := hWP.trans (inf_le_inf_right _ d.sylow_le_normalizer)
  have hwF : w ∈ e.F := by
    rw [← hea, e.fixed_join]
    exact mem_sup_left (mem_zpowers _)
  have hbound := e.normalizer_omega_elementary_centralizer_lower_bound h hN heproper w hwF
  change 64 ≤ Nat.card (We ⊓ centralizer ({w} : Set G) : Subgroup G) at hbound
  have hle : We ⊓ centralizer ({w} : Set G) ≤ e.F := by
    rw [heF]
    exact inf_le_inf_right _ hWV
  have hc := card_le_of_le hle
  rw [e.card] at hc
  omega

end Stellmacher.Recognition.ParrottSecondElementaryData
