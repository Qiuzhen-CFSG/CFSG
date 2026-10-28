module

public import Stellmacher.Recognition.Parrott.SecondCentralizerLocalStructure
public import Stellmacher.Recognition.Parrott.DerivedConjugacyCensus

/-!
# Local Sylow geometry for the second centralizer

For the supplied fixed involution v, put N=N_G(F), V=C_N(v),
W=Ω₁(O₂(N)), and P=T∩C_G(v), with all images taken in G.
The local order |V|=1536 and |N:T|=3 imply |P|=512: the
intersection has index at most three in V, and its order divides both
2048 and 1536. Hence P is the actual image of a Sylow two-subgroup
of V and contains W.

Since F≤W≤P and C_G(F)=F, Z(P) lies in the order-eight group Z(W).
It cannot equal Z(W), whose centralizer in N is W. The involutions z
and v generate a subgroup of order four in Z(P), so Z(P)=⟨z,v⟩.
We also retain the supplied fixed point's position in the original
H-conjugacy census, without replacing the chosen witnesses.

These are local conclusions; promotion from V to C_G(v) and the
remaining involution geometry are separate obligations.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678 and §4, p.682.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem involution_eq_of_mem_zpowers {v w : G}
    (hv : orderOf v = 2) (hw : orderOf w = 2) (hm : w ∈ zpowers v) : w = v := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hv] at hm
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hm
  have hnlt := Finset.mem_range.mp hn
  interval_cases n
  · have hw1 : w = 1 := by simpa using heq.symm
    simp [hw1] at hw
  · simpa using heq.symm

/-- The supplied fixed point has the derived-core membership and nonfusion
properties needed by the two-class census. -/
public theorem supplied_fixed_involution_census_position
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∃ t w : G, t ∈ E ∧ t ∉ zpowers z ∧ w ∈ E ∧ w ∉ zpowers z ∧
      Nat.card (H ⊓ centralizer ({t} : Set G) : Subgroup G) = 1024 ∧
      Nat.card (H ⊓ centralizer ({w} : Set G) : Subgroup G) = 512 ∧
      ((∃ a : H, (a : G) * t * (a : G)⁻¹ = v) ∨
        (∃ a : H, (a : G) * w * (a : G)⁻¹ = v)) := by
  intro H J E
  obtain ⟨t, w, htE, htz, hwE, hwz, htc, hwc, hcover⟩ :=
    parrott_derived_conjugacy_census z h
  have hvZ := (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).1
  have hvE : v ∈ E :=
    (d.normalizer_core_omega_structure h hN hproper).2.2.1 hvZ |>.1
  have hvC : v ∈ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) :=
    (hfix.symm ▸ mem_zpowers v).2
  have hvz : v ∉ zpowers z := by
    intro hvz
    have heq : v = z := involution_eq_of_mem_zpowers h.involution hv hvz
    exact (d.normalizer_three_fixed_not_isConj h hN hproper Q v hvC)
      (isConj_iff.mpr ⟨1, by simp [heq]⟩)
  rcases hcover v hvE hvz with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨t, w, htE, htz, hwE, hwz, htc, hwc, Or.inl ⟨a, ha⟩⟩
  · exact ⟨t, w, htE, htz, hwE, hwz, htc, hwc, Or.inr ⟨a, ha⟩⟩

/-- The local centralizer calculation, rewritten in ambient subgroup notation. -/
public theorem normalizer_fixed_local_image_structure
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let W := U.map (N.subtype.comp K.subtype)
    let C := centralizer ({v} : Set G)
    let V := N ⊓ C
    Nat.card V = 1536 ∧
      W ≤ V ∧
      ((pCore 2 (C.subgroupOf N)).map (C.subgroupOf N).subtype).map N.subtype = W ∧
      Nat.card (pCore 2 (C.subgroupOf N)) = 256 := by
  classical
  intro N K U W C V
  obtain ⟨hBcard, hcore, hcorecard, _⟩ :=
    d.normalizer_fixed_centralizer_structure h hN hproper Q v hv hfix
  have hmap : (C.subgroupOf N).map N.subtype = V := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.property, hb⟩
    · intro hx
      let b : C.subgroupOf N := ⟨⟨x, hx.1⟩, hx.2⟩
      exact mem_map_of_mem N.subtype b.property
  have hVcard : Nat.card V = 1536 := by
    rw [← hmap, card_map_of_injective N.subtype_injective]
    exact hBcard
  have hWle : W ≤ V := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hgeom :=
      (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).2.2.2.2
    have huG : (u : G) ∈ W := mem_map_of_mem (N.subtype.comp K.subtype) hu
    exact ⟨(K.subtype u).property, hgeom huG⟩
  refine ⟨hVcard, hWle, ?_, ?_⟩
  · rw [hcore]
  · exact hcorecard

/-- The intersection of the supplied Sylow subgroup with C_G(v) has order 512. -/
public theorem normalizer_fixed_sylow_card (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G) : Subgroup G) = 512 := by
  let N := normalizer (d.F : Set G)
  let T : Subgroup G := d.sylow
  let C := centralizer ({v} : Set G)
  let V := N ⊓ C
  let P := T ⊓ C
  have hTN : T ≤ N := d.sylow_le_normalizer
  have hPV : P ≤ V := inf_le_inf hTN le_rfl
  have hTcard : Nat.card T = 2048 := d.sylow_card h
  have hNcard : Nat.card N = 6144 := (d.normalizer_core_order h hN hproper).1
  have hVcard : Nat.card V = 1536 :=
    (d.normalizer_fixed_local_image_structure h hN hproper Q v hv hfix).1
  have hidx : T.relIndex N = 3 := by
    have hc := (T.subgroupOf N).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv, hTcard, hNcard] at hc
    change T.relIndex N * 2048 = 6144 at hc
    omega
  have hPVidx : (P.subgroupOf V).index ≤ 3 := by
    have heq : T ⊓ V = P := by
      dsimp [V, P]
      rw [← inf_assoc, inf_eq_left.mpr hTN]
    change P.relIndex V ≤ 3
    rw [← heq, inf_relIndex_right]
    exact (relIndex_le_of_le_right (show V ≤ N from inf_le_left) (by omega : T.relIndex N ≠ 0)).trans hidx.le
  have hPcard : Nat.card P ≤ 512 := by
    have hd := Nat.dvd_gcd (card_dvd_of_le (show P ≤ T from inf_le_left))
      (card_dvd_of_le hPV)
    rw [hTcard, hVcard] at hd
    exact Nat.le_of_dvd (by decide : 0 < 512) (by norm_num at hd ⊢; exact hd)
  have hc := (P.subgroupOf V).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hPV).toEquiv, hVcard] at hc
  change Nat.card P = 512
  nlinarith


/-- The center of the supplied local Sylow intersection is the plane ⟨z,v⟩. -/
public theorem normalizer_fixed_sylow_center (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    (center P).map P.subtype = zpowers z ⊔ zpowers v := by
  intro P
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  let U := omega₁ K (p := 2)
  let i := N.subtype.comp K.subtype
  let W := U.map i
  let Z := (center U).map (i.comp U.subtype)
  let ZP := (center P).map P.subtype
  let L := zpowers z ⊔ zpowers v
  have hi : Function.Injective i := N.subtype_injective.comp K.subtype_injective
  have hWcard : Nat.card W = 256 :=
    (card_map_of_injective hi).trans (d.normalizer_core_omega_structure h hN hproper).1
  have hZcard : Nat.card Z = 8 :=
    (card_map_of_injective (f := i.comp U.subtype) (hi.comp U.subtype_injective)).trans
      (d.normalizer_core_omega_structure h hN hproper).2.1
  have hPcard : Nat.card P = 512 := d.normalizer_fixed_sylow_card h hN hproper Q v hv hfix
  have hWP : W ≤ P := by
    rintro x ⟨u, hu, rfl⟩
    exact ⟨d.normalizer_core_le_sylow (mem_map_of_mem N.subtype u.property),
      (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).2.2.2.2
        (mem_map_of_mem i hu)⟩
  have hFW : d.F ≤ W := le_sup_right.trans
    (d.elementary_join_le_normalizer_core_omega h hN hproper)
  have hvF : v ∈ d.F := (hfix.symm ▸ mem_zpowers v).1
  have hZPZ : ZP ≤ Z := by
    rintro x ⟨p, hp, rfl⟩
    have hpF : (p : G) ∈ d.F := by
      rw [← d.centralizer_eq]
      intro y hy
      exact congrArg P.subtype (mem_center_iff.mp hp ⟨y, hWP (hFW hy)⟩)
    obtain ⟨u, hu, he⟩ := hFW hpF
    refine ⟨⟨u, hu⟩, ?_, he⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply hi
    have hh := congrArg P.subtype (mem_center_iff.mp hp
      ⟨i y.val, hWP (mem_map_of_mem i y.property)⟩)
    change i y.val * (p : G) = (p : G) * i y.val at hh
    change i (y.val * u) = i (u * y.val)
    simpa only [map_mul, he] using hh
  have hzZP : z ∈ ZP := by
    refine ⟨⟨z, d.le_sylow d.z_mem_inf.2, ?_⟩, ?_, rfl⟩
    · exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (d.sylow_le_centralizer (d.le_sylow hvF))).symm
    · apply mem_center_iff.mpr
      intro x
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (d.sylow_le_centralizer x.property.1)
  have hvZP : v ∈ ZP := by
    refine ⟨⟨v, d.le_sylow hvF, mem_centralizer_singleton_iff.mpr rfl⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp x.property.2
  have hLZP : L ≤ ZP := sup_le (zpowers_le.mpr hzZP) (zpowers_le.mpr hvZP)
  have hvz : v ∉ zpowers z := by
    intro hh
    exact (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).2.1
      ((zpowers_le.mpr d.z_mem_normalizer_core_center) hh)
  have hLcard : Nat.card L = 4 := by
    rw [show L = zpowers z ⊔ zpowers v from rfl,
      card_sup_zpowers_of_normalizing_involution (zpowers z) v
        (hv ▸ pow_orderOf_eq_one v) hvz, Nat.card_zpowers, h.involution]
    · exact (centralizer_le_normalizer (zpowers z : Set G)) (by
        rw [zpowers_eq_closure, centralizer_closure]
        exact d.sylow_le_centralizer (d.le_sylow hvF))
  have hne : ZP ≠ Z := by
    intro he
    have hPW : P ≤ W := by
      have heW : N ⊓ centralizer (Z : Set G) = W :=
        d.normalizer_omega_center_centralizer h hN hproper
      rw [← heW]
      intro x hx
      refine ⟨d.sylow_le_normalizer hx.1, ?_⟩
      rintro y hy
      rw [← he] at hy
      obtain ⟨yP, hyP, rfl⟩ := hy
      exact (congrArg P.subtype (mem_center_iff.mp hyP ⟨x, hx⟩)).symm
    have hh := card_le_of_le hPW
    rw [hPcard, hWcard] at hh
    omega
  have hZPcard : Nat.card ZP ≤ 4 := by
    have hd : Nat.card ZP ∣ 8 := hZcard ▸ card_dvd_of_le hZPZ
    have hlt : Nat.card ZP < 8 := by
      have hh := card_le_of_le hZPZ
      rw [hZcard] at hh
      apply lt_of_le_of_ne hh
      intro he
      exact hne (eq_of_le_of_card_ge hZPZ (by omega))
    have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  exact (eq_of_le_of_card_ge hLZP (by rw [hLcard]; exact hZPcard)).symm

/-- The order-512 intersection is an actual Sylow image in C_N(v), and
contains the ambient omega image. No Sylow assertion about C_G(v) is used. -/
public theorem normalizer_fixed_sylow_local_position
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let C := centralizer ({v} : Set G)
    let V := N ⊓ C
    let P := (d.sylow : Subgroup G) ⊓ C
    W ≤ P ∧ ∃ S : Sylow 2 V, (S : Subgroup V).map V.subtype = P := by
  intro N K W C V P
  have hWP : W ≤ P := by
    rintro x ⟨u, hu, rfl⟩
    exact ⟨d.normalizer_core_le_sylow (mem_map_of_mem N.subtype u.property),
      (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).2.2.2.2
        (mem_map_of_mem (N.subtype.comp K.subtype) hu)⟩
  have hPV : P ≤ V := inf_le_inf d.sylow_le_normalizer le_rfl
  have hcard : Nat.card (P.subgroupOf V) = 512 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPV).toEquiv).trans
      (d.normalizer_fixed_sylow_card h hN hproper Q v hv hfix)
  have hVcard : Nat.card V = 1536 :=
    (d.normalizer_fixed_local_image_structure h hN hproper Q v hv hfix).1
  have hidx : (P.subgroupOf V).index = 3 := by
    have hc := (P.subgroupOf V).index_mul_card
    rw [hcard, hVcard] at hc
    omega
  have hp : IsPGroup 2 (P.subgroupOf V) :=
    IsPGroup.of_card (n := 9) (by rw [hcard]; decide)
  exact ⟨hWP, hp.toSylow (by rw [hidx]; decide), map_subgroupOf_eq_of_le hPV⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
