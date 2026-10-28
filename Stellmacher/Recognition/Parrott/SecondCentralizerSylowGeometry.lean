module

public import Stellmacher.Recognition.Parrott.SecondCentralizerLocalSylow
public import Stellmacher.Recognition.Parrott.NormalizerElementaryFusion
public import Stellmacher.Recognition.Parrott.NormalizerElementaryCentralizer
public import Stellmacher.Recognition.Parrott.NormalizerInvolutionCosets

/-!
# Sylow geometry of the second centralizer

For the prescribed fixed involution v, the two-class census in E=O₂(H)′
identifies C_H(v) with the order-512 intersection P=T∩C_G(v).
The center formula Z(P)=⟨z,v⟩ then forces N_{C_G(v)}(P) to centralize z:
the other nonidentity possibilities v and zv are not conjugate to z.
Thus P is self-normalizing in C_G(v), and the normalizer-index congruence
promotes it to an actual Sylow two-subgroup, preserving P and v.

Two elements of E have a common centralizer of order at least 128 in J:
each centralizer has index at most two in the order-512 core. For an
involution in F outside Z(Ω₁(K)), the normalizer orbit moves it into E∩F
while keeping the transported v in Z(Ω₁(K))≤E. Elements of the omega
center centralize the whole order-256 omega subgroup. Finally, conjugation
by the supplied Q moves any omega involution into E∨F, whose involutions
lie in E or F. Since Q fixes v, this proves the required lower bound in
C_N(v), without an assertion that C_G(v) is contained in N.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678 and §4, p.682.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem centralizer_card_conj (H : Subgroup G) (a : H) (x : G) :
    Nat.card (H ⊓ centralizer ({(a : G) * x * (a : G)⁻¹} : Set G) : Subgroup G) =
      Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  let f := MulAut.conj (a : G)
  have hm : (centralizer ({x} : Set G)).map f.toMonoidHom =
      centralizer ({f x} : Set G) := by
    apply le_antisymm
    · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
        map_centralizer_le_centralizer_image ({x} : Set G) f.toMonoidHom
    · intro y hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      simpa only [map_mul, f.apply_symm_apply] using
        mem_centralizer_singleton_iff.mp hy
  have hH : H.map f.toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer a.property)
  have he : (H ⊓ centralizer ({x} : Set G) : Subgroup G).map f.toMonoidHom =
      H ⊓ centralizer ({f x} : Set G) := by rw [map_inf _ _ _ f.injective, hm, hH]
  change Nat.card (H ⊓ centralizer ({f x} : Set G) : Subgroup G) = _
  rw [← he, card_map_of_injective f.injective]

/-- The supplied fixed involution belongs to the smaller original centralizer class. -/
public theorem supplied_fixed_original_centralizer_card
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    Nat.card (centralizer ({z} : Set G) ⊓ centralizer ({v} : Set G) : Subgroup G) = 512 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  obtain ⟨t, w, htE, htz, hwE, hwz, htc, hwc, hcover⟩ :=
    parrott_derived_conjugacy_census z h
  obtain ⟨u, hu, huz, hu2, _, hzu, hcenter⟩ :=
    d.exists_normalizer_core_center_generator h hN hproper
  have huZ : u ∈ (center K).map (N.subtype.comp K.subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers u)
  have huc : 1024 ≤ Nat.card (H ⊓ centralizer ({u} : Set G) : Subgroup G) := by
    have he := d.normalizer_core_eq_sylow_centralizer h hN hproper u huZ huz
    have hc : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) = 1024 := by
      rw [← he, card_map_of_injective N.subtype_injective]
      exact (d.normalizer_core_order h hN hproper).2.1
    rw [← hc]
    exact card_le_of_le (inf_le_inf_right _ d.sylow_le_centralizer)
  have hzt : IsConj z t := by
    rcases hcover u hu.1 huz with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact hzu.trans (isConj_iff.mpr ⟨(a : G), ha⟩).symm
    · have hc := centralizer_card_conj H a w
      rw [ha, hwc] at hc
      omega
  have hvdata := d.normalizer_three_prescribed_fixed_generator h hN hproper Q v hv hfix
  have hvz : v ∉ zpowers z := by
    intro hh
    exact hvdata.2.1 ((zpowers_le.mpr d.z_mem_normalizer_core_center) hh)
  rcases hcover v hvdata.1.1 hvz with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact (hvdata.2.2.2 (hzt.trans (isConj_iff.mpr ⟨(a : G), ha⟩))).elim
  · have hc := centralizer_card_conj H a w
    rw [ha, hwc] at hc
    exact hc

private theorem zpowers_two_cases {x y : G} (hx : orderOf x = 2)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hx] at hy
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hy
  have hnlt := Finset.mem_range.mp hn
  interval_cases n
  · exact Or.inl (by simpa using heq.symm)
  · exact Or.inr (by simpa using heq.symm)

private theorem plane_cases {z v x : G} (hz : orderOf z = 2) (hv : orderOf v = 2)
    (hc : Commute z v) (hx : x ∈ zpowers z ⊔ zpowers v) :
    x = 1 ∨ x = z ∨ x = v ∨ x = z * v := by
  open scoped Pointwise in
  have he : ((zpowers z ⊔ zpowers v : Subgroup G) : Set G) =
      (zpowers z : Set G) * (zpowers v : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr
      ((Subgroup.centralizer_le_normalizer _) (by
        rw [zpowers_eq_closure, centralizer_closure]
        exact mem_centralizer_singleton_iff.mpr hc.symm.eq)))
  rw [← SetLike.mem_coe, he] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rcases zpowers_two_cases hz ha with rfl | rfl <;>
    rcases zpowers_two_cases hv hb with rfl | rfl <;> simp

/-- The normalizer of P inside the second centralizer fixes z. -/
public theorem normalizer_fixed_sylow_normalizer_le_original_centralizer
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    normalizer (P : Set G) ⊓ centralizer ({v} : Set G) ≤ centralizer ({z} : Set G) := by
  intro P a ha
  have hcenter := d.normalizer_fixed_sylow_center h hN hproper Q v hv hfix
  change (center P).map P.subtype = zpowers z ⊔ zpowers v at hcenter
  have hzZ : z ∈ (center P).map P.subtype := by
    rw [hcenter]
    exact mem_sup_left (mem_zpowers z)
  obtain ⟨zP, hzP, hez⟩ := hzZ
  change (zP : G) = z at hez
  let f := P.normalizerMonoidHom ⟨a, ha.1⟩
  have hchar := characteristic_iff_map_le.mp
    (inferInstance : (center P).Characteristic) f
  have hmem : a * z * a⁻¹ ∈ zpowers z ⊔ zpowers v := by
    rw [← hcenter]
    have hh := mem_map_of_mem P.subtype (hchar (mem_map_of_mem f.toMonoidHom hzP))
    change a * (zP : G) * a⁻¹ ∈ (center P).map P.subtype at hh
    rwa [hez] at hh
  have hvdata := d.normalizer_three_prescribed_fixed_generator h hN hproper Q v hv hfix
  have hvz : v ∉ zpowers z := by
    intro hh
    exact hvdata.2.1 ((zpowers_le.mpr d.z_mem_normalizer_core_center) hh)
  have hcomm : Commute z v :=
    (mem_centralizer_singleton_iff.mp (d.sylow_le_centralizer (d.le_sylow hvdata.1.2))).symm
  have hnot : ¬ IsConj z (z * v) := by
    obtain ⟨g, _, hg⟩ := parrott_derived_central_twist_conjugator z h v hvdata.1.1 hvz
    intro hh
    exact hvdata.2.2.2 (hh.trans (isConj_iff.mpr ⟨(g : G), hg⟩).symm)
  rcases plane_cases h.involution hv hcomm hmem with he | he | he | he
  · have hz1 : z = 1 := (MulAut.conj a).injective (he.trans (map_one _).symm)
    have hh := h.involution
    simp [hz1] at hh
  · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  · exact (hvdata.2.2.2 (isConj_iff.mpr ⟨a, he⟩)).elim
  · exact (hnot (isConj_iff.mpr ⟨a, he⟩)).elim

/-- The supplied intersection is a Sylow subgroup of the full second centralizer. -/
public theorem normalizer_fixed_sylow_ambient_position
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∃ R : Sylow 2 C, (R : Subgroup C).map C.subtype = P := by
  intro C P
  let H := centralizer ({z} : Set G)
  have hPH : P ≤ H ⊓ C := inf_le_inf_right _ d.sylow_le_centralizer
  have hPc : Nat.card P = 512 := d.normalizer_fixed_sylow_card h hN hproper Q v hv hfix
  have hHC : H ⊓ C = P := (eq_of_le_of_card_ge hPH (by
    rw [hPc, d.supplied_fixed_original_centralizer_card h hN hproper Q v hv hfix])).symm
  have hnorm : normalizer (P : Set G) ⊓ C ≤ P := by
    apply le_trans (le_inf (d.normalizer_fixed_sylow_normalizer_le_original_centralizer h hN hproper Q v hv hfix)
      inf_le_right) (le_of_eq hHC)
  let S := P.subgroupOf C
  have hS : Nat.card S = 2 ^ 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show P ≤ C from inf_le_right)).toEquiv, hPc]
    decide
  have hn : normalizer (S : Set C) = S := by
    apply le_antisymm _ S.le_normalizer
    rw [← subgroupOf_normalizer_eq (show P ≤ C from inf_le_right)]
    intro a ha
    exact hnorm ⟨ha, a.property⟩
  have hidx : S.relIndex (normalizer (S : Set C)) = 1 := by
    rw [hn]
    exact relIndex_eq_one.mpr le_rfl
  have hcongr := Sylow.card_quotient_normalizer_modEq_card_quotient hS
  have hodd : ¬ 2 ∣ S.index := by
    intro hd
    have hh := (hcongr.dvd_iff dvd_rfl).mpr hd
    change 2 ∣ S.relIndex (normalizer (S : Set C)) at hh
    rw [hidx] at hh
    norm_num at hh
  exact ⟨(IsPGroup.of_card hS).toSylow hodd, map_subgroupOf_eq_of_le inf_le_right⟩

private theorem derived_core_centralizer_lower_bound
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ l ∈ E, 256 ≤ Nat.card (J.map H.subtype ⊓ centralizer ({l} : Set G) : Subgroup G) := by
  intro H J E l hl
  by_cases hlz : l ∈ zpowers z
  · have hle : J.map H.subtype ≤ centralizer ({l} : Set G) := by
      intro x hx
      have hxH := map_subtype_le J hx
      have hxC : x ∈ centralizer (zpowers z : Set G) := by
        rw [zpowers_eq_closure, centralizer_closure]
        exact hxH
      exact mem_centralizer_singleton_iff.mpr (hxC l hlz).symm
    rw [inf_eq_left.mpr hle, card_map_of_injective H.subtype_injective, h.core_card]
    decide
  · rw [parrott_derived_core_centralizer_card z h l hl hlz]

/-- Any two elements of the original derived core have a common centralizer
of order at least 128 in the original core, hence in the second normalizer. -/
public theorem normalizer_derived_pair_centralizer_lower_bound
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    ∀ u ∈ E, ∀ l ∈ E,
      128 ≤ Nat.card (N ⊓ centralizer ({u} : Set G) ⊓ centralizer ({l} : Set G) : Subgroup G) := by
  intro H J E N u hu l hl
  let L := J.map H.subtype
  let B := L ⊓ centralizer ({u} : Set G)
  let A := L ⊓ centralizer ({l} : Set G)
  have hB : 256 ≤ Nat.card B := derived_core_centralizer_lower_bound h u hu
  have hA : 256 ≤ Nat.card A := derived_core_centralizer_lower_bound h l hl
  have hL : Nat.card L = 512 :=
    (card_map_of_injective H.subtype_injective).trans h.core_card
  have hidx : B.relIndex L ≤ 2 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) B L bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, hL] at hc
    nlinarith
  have hn : B.relIndex L ≠ 0 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) B L bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, hL] at hc
    intro hh
    rw [hh, mul_zero] at hc
    omega
  have hi : (B ⊓ A).relIndex A ≤ 2 := by
    rw [inf_relIndex_right]
    exact (relIndex_le_of_le_right (show A ≤ L from inf_le_left) hn).trans hidx
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ A) A bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left] at hc
  have hb : 128 ≤ Nat.card (B ⊓ A : Subgroup G) := by nlinarith
  apply hb.trans (card_le_of_le ?_)
  intro x hx
  exact ⟨⟨d.sylow_le_normalizer (d.core_le_sylow hx.1.1), hx.1.2⟩, hx.2.2⟩


omit [Finite G] in
private theorem pair_centralizer_card_conj (N : Subgroup G) (n : N) (u l : G) :
    Nat.card (N ⊓ centralizer ({(n : G) * u * (n : G)⁻¹} : Set G) ⊓
      centralizer ({(n : G) * l * (n : G)⁻¹} : Set G) : Subgroup G) =
    Nat.card (N ⊓ centralizer ({u} : Set G) ⊓ centralizer ({l} : Set G) : Subgroup G) := by
  let f := MulAut.conj (n : G)
  have hm (x : G) : (centralizer ({x} : Set G)).map f.toMonoidHom =
      centralizer ({f x} : Set G) := by
    apply le_antisymm
    · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
        map_centralizer_le_centralizer_image ({x} : Set G) f.toMonoidHom
    · intro y hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      simpa only [map_mul, f.apply_symm_apply] using
        mem_centralizer_singleton_iff.mp hy
  have hN : N.map f.toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.mp (N.le_normalizer n.property)
  have he : (N ⊓ centralizer ({u} : Set G) ⊓ centralizer ({l} : Set G) : Subgroup G).map
      f.toMonoidHom = N ⊓ centralizer ({f u} : Set G) ⊓ centralizer ({f l} : Set G) := by
    rw [map_inf _ _ _ f.injective, map_inf _ _ _ f.injective, hm, hm, hN]
  change Nat.card (N ⊓ centralizer ({f u} : Set G) ⊓ centralizer ({f l} : Set G) : Subgroup G) = _
  rw [← he, card_map_of_injective f.injective]

/-- Every element of F has centralizer of order at least 128 in C_N(v). -/
public theorem normalizer_fixed_elementary_centralizer_lower_bound
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let V := N ⊓ centralizer ({v} : Set G)
    ∀ l ∈ d.F, 128 ≤ Nat.card (V ⊓ centralizer ({l} : Set G) : Subgroup G) := by
  intro N V l hl
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let K := pCore 2 N
  let U := omega₁ K (p := 2)
  let i := N.subtype.comp K.subtype
  let W := U.map i
  let Z := (center U).map (i.comp U.subtype)
  have hi : Function.Injective i := N.subtype_injective.comp K.subtype_injective
  have hWcard : Nat.card W = 256 :=
    (card_map_of_injective hi).trans (d.normalizer_core_omega_structure h hN hproper).1
  have hZcard : Nat.card Z = 8 :=
    (card_map_of_injective (f := i.comp U.subtype) (hi.comp U.subtype_injective)).trans
      (d.normalizer_core_omega_structure h hN hproper).2.1
  have hZE : Z ≤ E ⊓ d.F := (d.normalizer_core_omega_structure h hN hproper).2.2.1
  have hvZ : v ∈ Z := (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).1
  have hWV : W ≤ V := (d.normalizer_fixed_local_image_structure h hN hproper Q v hv hfix).2.1
  by_cases hlZ : l ∈ Z
  · have hWC : W ≤ V ⊓ centralizer ({l} : Set G) := by
      refine le_inf hWV ?_
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
  obtain ⟨w, hw, hwZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hwcard := d.normalizer_elementary_outside_omega_center_centralizer_card
    h hN hproper w hw hwZ
  obtain ⟨n, hn⟩ := d.normalizer_elementary_outside_omega_center_fusion_of_centralizer_card
    h hN hproper w hw.2 hwZ hwcard l hl hlZ
  let u := (n : G)⁻¹ * v * (n : G)
  have huZ : u ∈ Z := by
    have hh := (mem_normalizer_iff.mp
      (d.normalizer_core_centers_normalized.2 (N.inv_mem n.property)) v).mp hvZ
    simpa only [inv_inv] using hh
  have hc := d.normalizer_derived_pair_centralizer_lower_bound h u (hZE huZ).1 w hw.1
  have he := pair_centralizer_card_conj N n u w
  have heu : (n : G) * u * (n : G)⁻¹ = v := by dsimp [u]; group
  rw [heu, hn] at he
  exact he.symm ▸ hc

/-- The supplied Q transports the derived and elementary calculations to
all involutions in the actual omega image. -/
public theorem normalizer_fixed_omega_centralizer_lower_bound
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let V := N ⊓ centralizer ({v} : Set G)
    ∀ l ∈ W, orderOf l = 2 →
      128 ≤ Nat.card (V ⊓ centralizer ({l} : Set G) : Subgroup G) := by
  intro N K X D A hCD v hv hfix W V l hl hl2
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hWX : W ≤ X := by
    rw [show W = ((omega₁ K (p := 2)).map K.subtype).map N.subtype from (map_map _ _ _).symm]
    exact map_mono (map_subtype_le _)
  obtain ⟨q, hq⟩ := d.normalizer_core_involution_transport h hN hproper Q hCD l (hWX hl)
    (hl2 ▸ pow_orderOf_eq_one l)
  let y := ((q : N) : G) * l * ((q : N) : G)⁻¹
  have hy2 : y ^ 2 = 1 := by
    change (MulAut.conj ((q : N) : G) l) ^ 2 = 1
    rw [← map_pow, ← hl2, pow_orderOf_eq_one, map_one]
  have hvE : v ∈ E :=
    (d.normalizer_three_prescribed_fixed_generator h hN hproper Q v hv hfix).1.1
  have hb : 128 ≤ Nat.card (V ⊓ centralizer ({y} : Set G) : Subgroup G) := by
    rcases d.elementary_join_involution h y hq hy2 with hy | hy
    · exact d.normalizer_derived_pair_centralizer_lower_bound h v hvE y hy
    · exact d.normalizer_fixed_elementary_centralizer_lower_bound h hN hproper Q v hv hfix y hy
  have hqv : ((q : N) : G) * v * ((q : N) : G)⁻¹ = v := by
    have hvC : v ∈ centralizer (A : Set G) := (hfix.symm ▸ mem_zpowers v).2
    exact mul_inv_eq_iff_eq_mul.mpr (hvC ((q : N) : G)
      (mem_map_of_mem N.subtype q.property))
  have he := pair_centralizer_card_conj N (q : N) v l
  rw [hqv] at he
  exact he ▸ hb

/-- The ambient Sylow position and the omega-involution centralizer bound,
with all supplied local witnesses retained. -/
public theorem normalizer_fixed_sylow_omega_geometry
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let C := centralizer ({v} : Set G)
    let V := N ⊓ C
    let P := (d.sylow : Subgroup G) ⊓ C
    (∃ R : Sylow 2 C, (R : Subgroup C).map C.subtype = P) ∧
      ∀ l ∈ W, orderOf l = 2 →
        128 ≤ Nat.card (V ⊓ centralizer ({l} : Set G) : Subgroup G) := by
  intro N K X D A hCD v hv hfix W C V P
  exact ⟨d.normalizer_fixed_sylow_ambient_position h hN hproper Q v hv hfix,
    d.normalizer_fixed_omega_centralizer_lower_bound h hN hproper Q hCD v hv hfix⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
