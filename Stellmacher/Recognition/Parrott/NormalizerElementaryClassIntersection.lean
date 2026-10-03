module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeFixed
public import Stellmacher.Recognition.Parrott.DerivedConjugacyCensus

/-!
# The fixed involution's class meets the elementary complement

Put H=C_G(z), J=O₂(H), E=J′ in G, N=N_G(F), K=O₂(N), and
U=Ω₁(K). The prescribed generator v of C_F(Q) has an H-conjugate in
(E∩F) minus the ambient image of Z(U). The conjugator remains in H.

Choose t in Z(K) conjugate to z under Q. Since K centralizes t, the
conjugacy census puts t in the ten-element H-class. The fixed involution
v is not G-conjugate to z, so it belongs to the other class. If its class
missed (E∩F) minus Z(U), all eight points of that complement would be
in the class of t. That class also contains t and zt in Z(U), forcing
its entire ten-element orbit into E∩F.

This is impossible: for the supplied Sylow five-action, adjoining Z(J)
to the orbit of a noncentral derived element generates all of J′.
Indeed the generated subgroup has two fixed points and order dividing
32, hence has order two or 32 by the fixed-point congruence modulo five.
It contains a noncentral element and thus has order 32, whereas E∩F
has order sixteen. This implements the irreducibility argument directly
on J′ and needs no normalizer-centralizer calculation.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.674 and 677, the two derived classes and the elementary fusion paragraph.
-/

open Subgroup MulAction
namespace Stellmacher.Recognition

private theorem derived_class_not_contained
    {G : Type*} [Group G] [Finite G] (z : G) (h : ParrottCentralizerHypotheses z)
    (B : Subgroup G) (hB : Nat.card B = 16) (hzB : z ∈ B) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t ∈ E, t ∉ zpowers z → ∃ a : H, (a : G) * t * (a : G)⁻¹ ∉ B := by
  classical
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro H J E t ht htz
  by_contra! hall
  obtain ⟨tJ, htD, rfl⟩ := ht
  let i := H.subtype.comp J.subtype
  have hi : Function.Injective i := H.subtype_injective.comp J.subtype_injective
  obtain ⟨hZmap, _, _, _, hUpper, _, hDcard, _⟩ := parrott_centralizer_structure z h
  change Nat.card (commutator J) = 32 at hDcard
  have hZcard : Nat.card (center J) = 2 := by
    have hc := card_map_of_injective (K := center J) hi
    rw [hZmap, Nat.card_zpowers, h.involution] at hc
    exact hc.symm
  have hZD : center J ≤ commutator J := by
    rw [hUpper, ← Subgroup.upperCentralSeries_one]
    exact Subgroup.upperCentralSeries_mono J (by decide : 1 ≤ 2)
  obtain ⟨P, hPfix⟩ := h.five_centralizer
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, (h.card_and_solvable z).1]
    decide +kernel
  let : MulDistribMulAction P J := conjMulDistribMulActionOfLeNormalizer
    (P : Subgroup H) J (le_normalizer_of_normal (H := J))
  let : IsInvariant P J (commutator J) := isInvariant_of_characteristic _
  let : IsInvariant P J (center J) := isInvariant_of_characteristic _
  let L := closure (orbit P tJ)
  have hforward (a : P) (x : J) (hx : x ∈ L) : a • x ∈ L := by
    refine closure_induction (p := fun x _ => a • x ∈ L) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨b, rfl⟩
      exact subset_closure ⟨a * b, mul_smul a b tJ⟩
    · simpa only [smul_one] using L.one_mem
    · intro x y _ _ hx hy
      simpa only [smul_mul'] using L.mul_mem hx hy
    · intro x _ hx
      simpa only [smul_inv'] using L.inv_mem hx
  let : IsInvariant P J L := ⟨fun a x => ⟨hforward a x, fun hx => by
    simpa only [inv_smul_smul] using hforward a⁻¹ (a • x) hx⟩⟩
  let S := L ⊔ center J
  let : IsInvariant P J S := isInvariant_sup L (center J)
  have hLS : L ≤ S := le_sup_left
  have hZS : center J ≤ S := le_sup_right
  have htS : tJ ∈ S := hLS (subset_closure (mem_orbit_self tJ))
  have hSD : S ≤ commutator J := by
    apply sup_le _ hZD
    apply (closure_le _).mpr
    rintro _ ⟨p, rfl⟩
    exact (IsInvariant.invariant p tJ).mp htD
  have hSB : S.map i ≤ B := by
    rw [map_le_iff_le_comap]
    apply sup_le
    · apply (closure_le _).mpr
      rintro _ ⟨p, rfl⟩
      exact hall (p : H)
    · intro x hx
      exact (zpowers_le.mpr hzB) (hZmap ▸ mem_map_of_mem i hx)
  have hScard : Nat.card S ≤ 16 := by
    have hc := card_le_of_le hSB
    rwa [card_map_of_injective hi, hB] at hc
  have hfixed : (FixedPoints.subgroup P S).map S.subtype = center J := by
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      apply hPfix
      intro p hp
      have hh := congrArg (fun s : S => ((s : J) : H)) (hs ⟨p, hp⟩)
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro x hx
      refine ⟨⟨x, hZS hx⟩, ?_, rfl⟩
      intro p
      apply Subtype.ext
      apply hi
      have hxz : i x ∈ zpowers z := hZmap ▸ mem_map_of_mem i hx
      have hpz : ((p : H) : G) ∈ centralizer (zpowers z : Set G) := by
        rw [zpowers_eq_closure, centralizer_closure]
        exact (p : H).property
      change ((p : H) : G) * i x * ((p : H) : G)⁻¹ = i x
      exact mul_inv_eq_iff_eq_mul.mpr (hpz (i x) hxz).symm
  have hfixedcard : Nat.card (FixedPoints.subgroup P S) = 2 := by
    rw [← card_map_of_injective (K := FixedPoints.subgroup P S) S.subtype_injective,
      hfixed, hZcard]
  have hp : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by simpa using hPcard)
  have hmod := hp.card_modEq_card_fixedPoints S
  change Nat.ModEq 5 (Nat.card S) (Nat.card (FixedPoints.subgroup P S)) at hmod
  rw [hfixedcard] at hmod
  have hdiv : Nat.card S ∣ 2 ^ 5 := by
    simpa only [hDcard, show 2 ^ 5 = (32 : ℕ) by decide] using card_dvd_of_le hSD
  obtain ⟨n, hn, hSn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hS2 : Nat.card S = 2 := by
    rw [hSn] at hmod hScard ⊢
    interval_cases n
    · norm_num [Nat.ModEq] at hmod
    · rfl
    · norm_num [Nat.ModEq] at hmod
    · norm_num [Nat.ModEq] at hmod
    · norm_num [Nat.ModEq] at hmod
    · norm_num at hScard
  have hSZ : S = center J := (eq_of_le_of_card_ge hZS (by omega)).symm
  exact htz (hZmap ▸ mem_map_of_mem i (hSZ ▸ htS))

private theorem local_class_card
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) (x : G) :
    (Set.range (fun a : H => (a : G) * x * (a : G)⁻¹)).ncard *
      Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) = Nat.card H := by
  let act : MulDistribMulAction H G := MulDistribMulAction.compHom G
    ((MulAut.conj : G →* MulAut G).comp H.subtype)
  let : MulAction H G := act.toMulAction
  have heq : (stabilizer H x).map H.subtype = H ⊓ centralizer ({x} : Set G) := by
    ext a
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp ha)⟩
    · rintro ⟨haH, ha⟩
      exact ⟨⟨a, haH⟩, mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp ha), rfl⟩
  have hc := Nat.card_congr (orbitProdStabilizerEquivGroup H x)
  rw [Nat.card_prod, ← card_map_of_injective (K := stabilizer H x)
    H.subtype_injective, heq] at hc
  exact hc

private theorem local_class_eq
    {G : Type*} [Group G] (H : Subgroup G) (x y : G)
    (hxy : ∃ a : H, (a : G) * x * (a : G)⁻¹ = y) :
    Set.range (fun a : H => (a : G) * x * (a : G)⁻¹) =
      Set.range (fun a : H => (a : G) * y * (a : G)⁻¹) := by
  obtain ⟨a, rfl⟩ := hxy
  ext w
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · rintro ⟨b, rfl⟩
    refine ⟨b * a, ?_⟩
    simp only [Subgroup.coe_mul]
    group

end Stellmacher.Recognition

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- The H-class of the supplied Q-fixed involution meets the eight-element
complement of the omega center inside E∩F, with an actual H-conjugator. -/
public theorem normalizer_fixed_class_meets_elementary_complement
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    ∃ w : G, w ∈ E ⊓ d.F ∧ w ∉ ZU ∧
      ∃ a : H, (a : G) * v * (a : G)⁻¹ = w := by
  classical
  intro H J E N K U ZU
  let B := E ⊓ d.F
  let ZK := (center K).map (N.subtype.comp K.subtype)
  let A := (Q : Subgroup N).map N.subtype
  have hvFC : v ∈ d.F ⊓ centralizer (A : Set G) := hfix ▸ mem_zpowers v
  have hvZU : v ∈ ZU := by
    have heq := d.normalizer_three_fixed_elementary h hN hproper Q
    exact (heq ▸ hvFC).1
  have hZUB : ZU ≤ B := (d.normalizer_core_omega_structure h hN hproper).2.2.1
  have hvB : v ∈ B := hZUB hvZU
  have hvnc : ¬ IsConj z v :=
    d.normalizer_three_fixed_not_isConj h hN hproper Q v hvFC.2
  have hvz : v ∉ zpowers z := by
    intro hh
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hh
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hh
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · have hv1 : v = 1 := by simpa using heq.symm
      simp [hv1] at hv
    · have hvz : v = z := by simpa using heq.symm
      exact hvnc (hvz ▸ IsConj.refl z)
  obtain ⟨t, htB, htz, _, hqt, hZK⟩ :=
    d.exists_normalizer_three_center_generator h hN hproper Q
  change ZK = zpowers z ⊔ zpowers t at hZK
  have htZK : t ∈ ZK := by rw [hZK]; exact mem_sup_right (mem_zpowers t)
  have htZU : t ∈ ZU := d.normalizer_core_omega_inclusions.2.1 htZK
  have hzZU : z ∈ ZU :=
    d.normalizer_core_omega_inclusions.2.1 d.z_mem_normalizer_core_center
  have hzt : IsConj z t := by
    obtain ⟨q, hq⟩ := hqt
    exact isConj_iff.mpr ⟨((q : N) : G), hq⟩
  have hCt : 1024 ≤ Nat.card (H ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    have hXC : K.map N.subtype ≤ H ⊓ centralizer ({t} : Set G) := by
      rw [d.normalizer_core_eq_sylow_centralizer h hN hproper t htZK htz]
      exact inf_le_inf_right _ d.sylow_le_centralizer
    have hc := card_le_of_le hXC
    rwa [card_map_of_injective N.subtype_injective,
      (d.normalizer_core_order h hN hproper).2.1] at hc
  let O (x : G) : Set G := Set.range (fun a : H => (a : G) * x * (a : G)⁻¹)
  have hcount (x : G) : (O x).ncard *
      Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) = 10240 :=
    (local_class_card H x).trans (h.card_and_solvable z).1
  obtain ⟨r, s, hrE, hrz, hsE, hsz, hCr, hCs, hcover⟩ :=
    parrott_derived_conjugacy_census z h
  have hOr : (O r).ncard = 10 := by
    have hc := hcount r
    rw [hCr] at hc
    omega
  have hOs : (O s).ncard = 20 := by
    have hc := hcount s
    rw [hCs] at hc
    omega
  have hrt : ∃ a : H, (a : G) * r * (a : G)⁻¹ = t := by
    rcases hcover t htB.1 htz with hh | hh
    · exact hh
    · have heq : O s = O t := local_class_eq H s t hh
      have hc := hcount t
      rw [← heq, hOs] at hc
      omega
  have hrtG : IsConj r t := by
    obtain ⟨a, ha⟩ := hrt
    exact isConj_iff.mpr ⟨a, ha⟩
  have hsv : ∃ a : H, (a : G) * s * (a : G)⁻¹ = v := by
    rcases hcover v hvB.1 hvz with hh | hh
    · obtain ⟨a, ha⟩ := hh
      exact (hvnc (hzt.trans (hrtG.symm.trans (isConj_iff.mpr ⟨a, ha⟩)))).elim
    · exact hh
  have hOt : (O t).ncard = 10 := by
    rw [← show O r = O t from local_class_eq H r t hrt]
    exact hOr
  have hcover' (x : G) (hx : x ∈ E) (hxz : x ∉ zpowers z) : x ∈ O t ∪ O v := by
    have hh := hcover x hx hxz
    change x ∈ O r ∪ O s at hh
    rwa [show O r = O t from local_class_eq H r t hrt,
      show O s = O v from local_class_eq H s v hsv] at hh
  have hBcard : (B : Set G).ncard = 16 := d.inf_card
  have hZUcard : (ZU : Set G).ncard = 8 :=
    (card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
      U.subtype_injective)).trans (d.normalizer_core_omega_structure h hN hproper).2.1
  have hdiff : ((B : Set G) \ ZU).ncard = 8 := by
    rw [Set.ncard_sdiff hZUB, hBcard, hZUcard]
  have htO : t ∈ O t := ⟨1, by simp⟩
  have hztO : z * t ∈ O t := by
    obtain ⟨a, _, ha⟩ := parrott_derived_central_twist_conjugator z h t htB.1 htz
    exact ⟨a, ha⟩
  have hpair : ({t, z * t} : Set G) ⊆ O t ∩ ZU := by
    intro x hx
    rcases (show x = t ∨ x = z * t by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with rfl | rfl
    · exact ⟨htO, htZU⟩
    · exact ⟨hztO, ZU.mul_mem hzZU htZU⟩
  have htne : t ≠ z * t := by
    intro heq
    have hz1 : z = 1 := mul_right_cancel (heq.symm.trans (one_mul t).symm)
    have hh := h.involution
    simp [hz1] at hh
  have hinter : 2 ≤ (O t ∩ (ZU : Set G)).ncard := by
    have hh := Set.ncard_le_ncard hpair
    rwa [Set.ncard_pair htne] at hh
  have hsmall : (O t \ (ZU : Set G)).ncard ≤ 8 := by
    have hh := Set.ncard_inter_add_ncard_sdiff_eq_ncard (O t) (ZU : Set G)
    rw [hOt] at hh
    omega
  by_contra! hnone
  have hsub : (B : Set G) \ ZU ⊆ O t \ (ZU : Set G) := by
    intro w hw
    refine ⟨?_, hw.2⟩
    have hwz : w ∉ zpowers z := fun hh => hw.2 ((zpowers_le.mpr hzZU) hh)
    rcases hcover' w hw.1.1 hwz with ht | hv
    · exact ht
    · obtain ⟨a, ha⟩ := hv
      exact (hnone w hw.1 hw.2 a ha).elim
  have heq : (B : Set G) \ ZU = O t \ (ZU : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (by omega)
  have hOB : O t ⊆ B := by
    intro w hw
    by_cases hwZU : w ∈ ZU
    · exact hZUB hwZU
    · exact (heq.symm ▸ (show w ∈ O t \ (ZU : Set G) from ⟨hw, hwZU⟩)).1
  obtain ⟨a, ha⟩ := derived_class_not_contained z h B d.inf_card d.z_mem_inf t htB.1 htz
  exact ha (hOB ⟨a, rfl⟩)

end Stellmacher.Recognition.ParrottSecondElementaryData
