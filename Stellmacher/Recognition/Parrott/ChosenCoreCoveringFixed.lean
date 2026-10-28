module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterIndexTwo
public import Theory.GroupAction.FixedLineIndecomposable

/-!
# Fixed points in the center of the covering centralizer

Put C = K ∩ S and A = C_E(C). The central commutator pairing gives
|A| |C| = 512. Since |C| ≤ 64, A has at least eight elements, contains
⟨z⟩, and is normalized by S. These are the local inputs for identifying
the fixed line of an order-four actor on E/⟨z⟩ inside A/⟨z⟩.
Thus C_E(y) centralizes C. The image of y generates S/C, so C_E(y)
lies in Z(S). Only the original local hypotheses are used.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the center calculation on p.676.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The annihilator of the core intersection is a large invariant subgroup
of the chosen centralizer containing the distinguished central line. -/
public theorem chosen_core_annihilator_geometry
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let C := K ⊓ S
    let A := E ⊓ centralizer (C : Set G)
    A ≤ S ∧ S ≤ normalizer (A : Set G) ∧ zpowers z ≤ A ∧ 8 ≤ Nat.card A := by
  intro H J K E S C A
  have hnorm (R : Subgroup H) [R.Normal] : H ≤ normalizer (R.map H.subtype : Set G) := by
    have hh := R.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hHK : H ≤ normalizer (K : Set G) := hnorm J
  have hHE : H ≤ normalizer (E : Set G) := by
    have hh := hnorm ((commutator J).map J.subtype)
    simpa only [map_map] using hh
  have hSC : S ≤ normalizer (C : Set G) :=
    (le_inf (inf_le_left.trans hHK) S.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hScentral : S ≤ normalizer (centralizer (C : Set G) : Set G) :=
    hSC.trans (le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer (C : Set G)))
  have hSA : S ≤ normalizer (A : Set G) :=
    (le_inf (inf_le_left.trans hHE) hScentral).trans inf_normalizer_le_normalizer_inf
  have hAS : A ≤ S := by
    intro a ha
    have hEH : E ≤ H := by
      rintro x ⟨j, _, rfl⟩
      exact j.val.property
    refine ⟨hEH ha.1, mem_centralizer_singleton_iff.mpr ?_⟩
    have haC : (d.a : G) ∈ C :=
      ⟨mem_map_of_mem H.subtype d.a_mem_core,
        d.a.property, mem_centralizer_singleton_iff.mpr rfl⟩
    exact (ha.2 (d.a : G) haC).symm
  refine ⟨hAS, hSA, zpowers_le.mpr ⟨d.z_mem_inf.1, ?_⟩, ?_⟩
  · intro c hc
    exact mem_centralizer_singleton_iff.mp hc.2.1
  · have hm := d.chosen_core_derived_centralizer_card_mul h
    have hc := d.chosen_core_intersection_card_le h
    change Nat.card A * Nat.card C = 512 at hm
    change Nat.card C ≤ 64 at hc
    nlinarith

/-- The derived fixed subgroup of a covering actor centralizes the core
intersection, by the unique fixed line on the derived central quotient. -/
public theorem chosen_covering_fixed_le_annihilator
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    ∀ y : H, (y : G) ∈ S → orderOf (QuotientGroup.mk' J y) = 4 →
      E ⊓ centralizer ({(y : G)} : Set G) ≤
        E ⊓ centralizer ((K ⊓ S : Subgroup G) : Set G) := by
  classical
  intro H J K E S y hyS hy
  let D := commutator J
  let ZD := (center J).subgroupOf D
  let W := D ⧸ ZD
  let q := QuotientGroup.mk' ZD
  let qJ := QuotientGroup.mk' J
  let e : D →* G := (H.subtype.comp J.subtype).comp D.subtype
  let C := K ⊓ S
  let A := E ⊓ centralizer (C : Set G)
  obtain ⟨hAS, hSA, hzA, hAcard⟩ := d.chosen_core_annihilator_geometry h
  change A ≤ S at hAS
  change S ≤ normalizer (A : Set G) at hSA
  change zpowers z ≤ A at hzA
  change 8 ≤ Nat.card A at hAcard
  obtain ⟨hZmap, _, _, _, hUpper, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 W := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := (Group.exponent_quotient_dvd ZD).trans
      (IsElementaryAbelian.exponent_dvd_p 2 D) }
  change D = Subgroup.upperCentralSeries J 2 at hUpper
  have hZD : center J ≤ D := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono J (show 1 ≤ 2 by decide)
  have hZimage : ZD.map e = zpowers z := by
    change ZD.map ((H.subtype.comp J.subtype).comp D.subtype) = zpowers z
    rw [← map_map, map_subgroupOf_eq_of_le hZD]
    exact hZmap
  have herange : e.range = E := by
    rw [MonoidHom.range_comp, D.range_subtype]
  let AD := A.comap e
  let B := AD.map q
  have hADimage : AD.map e = A := map_comap_eq_self (herange ▸ inf_le_left)
  have hZAD : ZD ≤ AD := by
    intro v hv
    exact hzA (hZimage ▸ mem_map_of_mem e hv)
  have hBne : B ≠ ⊥ := by
    intro hB
    have hAD : AD ≤ ZD := by
      have hh := (map_eq_bot_iff AD).mp hB
      rwa [QuotientGroup.ker_mk'] at hh
    have hAZ : A ≤ zpowers z := by
      rw [← hADimage, ← hZimage]
      exact map_mono hAD
    have hc := card_le_of_le hAZ
    rw [Nat.card_zpowers, h.involution] at hc
    omega
  obtain ⟨f, hf, hformula⟩ := parrott_derived_quotient_action z h
  let ι : H →* normalizer (J : Set H) :=
    (MonoidHom.id H).codRestrict _ (by intro u; rw [normalizer_eq_top]; trivial)
  let jAct : H →* MulAut J := J.normalizerMonoidHom.comp ι
  let : MulDistribMulAction H J := MulDistribMulAction.compHom J jAct
  let : IsInvariant H J D := isInvariant_of_characteristic D
  let action : H →* MulAut D := MulDistribMulAction.toMulAut H D
  let inc : S →* H := inclusion inf_le_left
  let rho : S →* MulAut W := f.comp (qJ.comp inc)
  let : MulDistribMulAction S W := MulDistribMulAction.compHom W rho
  have hequiv (s : S) (v : D) : s • q v = q (action (inc s) v) :=
    hformula (inc s) v (action (inc s) v) rfl
  have hpres (s : S) (w : W) (hw : w ∈ B) : s • w ∈ B := by
    obtain ⟨v, hv, rfl⟩ := hw
    rw [hequiv]
    refine mem_map_of_mem q ?_
    change e (action (inc s) v) ∈ A
    exact (hSA s.property (e v)).mp hv
  let : IsInvariant S W B := ⟨fun s w => ⟨hpres s w, fun hw => by
    have hh := hpres s⁻¹ (s • w) hw
    simpa only [inv_smul_smul] using hh⟩⟩
  let F := FixedPoints.subgroup (zpowers (f (qJ y))) W
  have hF : FixedPoints.subgroup S W ≤ F := by
    intro w hw
    apply (MulAut.mem_fixed_zpowers_iff _ _).mpr
    exact hw (⟨(y : G), hyS⟩ : S)
  have hFcard : Nat.card F ≤ 2 := parrott_derived_quotient_four_fixed_card_le z h f hf y hy
  have hFB : F ≤ B := subgroup_le_invariant_of_fixed_le_of_card_le_two
    (d.chosen_centralizer_isPGroup h) F hF hFcard B hBne
  rintro x ⟨⟨v, hv, rfl⟩, hxy⟩
  let vD : D := ⟨v, hv⟩
  have hyv : action y vD = vD := by
    apply Subtype.ext
    apply Subtype.ext
    apply H.subtype_injective
    change (y : G) * e vD * (y : G)⁻¹ = e vD
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hxy).symm
  have hvF : q vD ∈ F := by
    apply (MulAut.mem_fixed_zpowers_iff _ _).mpr
    rw [hformula y vD (action y vD) rfl, hyv]
  have hvB := hFB hvF
  have hcomap : B.comap q = AD :=
    comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hZAD)
  have hvAD : vD ∈ AD := hcomap ▸ hvB
  exact hvAD

private theorem chosen_covering_annihilator_fixed_le_center
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    ∀ y : H, (y : G) ∈ S → orderOf (QuotientGroup.mk' J y) = 4 →
      S ⊓ centralizer ((K ⊓ S : Subgroup G) : Set G) ⊓
        centralizer ({(y : G)} : Set G) ≤ (center S).map S.subtype := by
  intro H J K S y hyS hy
  let L := S.subgroupOf H
  let q := QuotientGroup.mk' J
  have hLcard : Nat.card (L.map q) ≤ 4 := by
    have hrel : K.relIndex S = Nat.card (L.map q) := by
      calc
        _ = (J.map H.subtype).relIndex (L.map H.subtype) := by
          rw [map_subgroupOf_eq_of_le (show S ≤ H from inf_le_left)]
        _ = J.relIndex L := relIndex_map_map_of_injective J L H.subtype_injective
        _ = Nat.card (L.map q) := by
          have hh := relIndex_ker L q
          rw [QuotientGroup.ker_mk'] at hh
          exact hh
    rw [← hrel]
    exact (d.chosen_core_relIndex_bounds h).2
  have hgen : zpowers (q y) = L.map q :=
    eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem q hyS))
      (by rw [Nat.card_zpowers, hy]; exact hLcard)
  rintro x ⟨⟨hxS, hxC⟩, hxy⟩
  refine ⟨⟨x, hxS⟩, mem_center_iff.mpr ?_, rfl⟩
  intro s
  let sH : H := ⟨s, s.property.1⟩
  have hsQ : q sH ∈ zpowers (q y) := hgen ▸ mem_map_of_mem q s.property
  obtain ⟨n, hn⟩ := hsQ
  let k : H := sH * y ^ (-n)
  have hkJ : k ∈ J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (sH * y ^ (-n)) = 1
    rw [map_mul, map_zpow, ← hn, zpow_neg, mul_inv_cancel]
  have hkS : (k : G) ∈ S := S.mul_mem s.property (S.zpow_mem hyS (-n))
  have hkC : (k : G) ∈ K ⊓ S := ⟨mem_map_of_mem H.subtype hkJ, hkS⟩
  have hxk : Commute x (k : G) := (hxC (k : G) hkC).symm
  have hxy' : Commute x (y : G) := mem_centralizer_singleton_iff.mp hxy
  have hxs := hxk.mul_right (hxy'.zpow_right n)
  have hprod : (k : G) * (y : G) ^ n = (s : G) := by
    change ((s : G) * (y : G) ^ (-n)) * (y : G) ^ n = (s : G)
    rw [zpow_neg, mul_assoc, inv_mul_cancel, mul_one]
  apply Subtype.ext
  change (s : G) * x = x * (s : G)
  rw [← hprod]
  exact hxs.symm.eq

/-- For an actor in the chosen centralizer whose image modulo the core has
order four, its fixed subgroup in the derived core lies in the chosen center.
No assertion about the order of the lift, fusion, or normalizer growth is used. -/
public theorem chosen_covering_fixed_le_center
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    ∀ y : H, (y : G) ∈ S → orderOf (QuotientGroup.mk' J y) = 4 →
      E ⊓ centralizer ({(y : G)} : Set G) ≤ (center S).map S.subtype := by
  intro H J E S y hyS hy
  have hfixed := d.chosen_covering_fixed_le_annihilator h y hyS hy
  have hAS := (d.chosen_core_annihilator_geometry h).1
  apply le_trans ?_ (d.chosen_covering_annihilator_fixed_le_center h y hyS hy)
  intro x hx
  exact ⟨⟨hAS (hfixed hx), (hfixed hx).2⟩, hx.2⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
