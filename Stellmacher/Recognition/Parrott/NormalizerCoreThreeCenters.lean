module

public import Stellmacher.Recognition.Parrott.NormalizerCoreOmega
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Sylow-three action on the second normalizer core

For the supplied F and T, set N=N_G(F), K=O₂(N), and U=Ω₁(K).
A Sylow three-subgroup of N has order three and cannot centralize z,
since C_N(z)=T is a two-group. Its action on the central four-group
therefore supplies a compatible conjugate t of z. Counting conjugation
orbits on Z(U) supplies the fixed involution v.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, Lemma 6 and the subsequent Sylow-three paragraphs.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Every actual Sylow three-subgroup of N has order three. -/
public theorem normalizer_three_card (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) : Nat.card Q = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, (d.normalizer_core_order h hN hproper).1,
    show 6144 = 2 ^ 11 * 3 by decide,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]

/-- The actual ambient image of Q does not centralize z. -/
public theorem normalizer_three_not_centralizes (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    ¬ (Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype ≤ centralizer ({z} : Set G) := by
  intro hQ
  let N := normalizer (d.F : Set G)
  have hle : (Q : Subgroup N).map N.subtype ≤ (d.sylow : Subgroup G) := by
    rw [← d.normalizer_inf_centralizer h]
    exact le_inf (map_subtype_le _) hQ
  have hd := card_dvd_of_le hle
  rw [card_map_of_injective N.subtype_injective,
    d.normalizer_three_card h hN hproper Q, d.sylow_card h] at hd
  norm_num at hd

omit [Finite G] in
/-- N normalizes both actual ambient centers. -/
public theorem normalizer_core_centers_normalized (d : ParrottSecondElementaryData z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    N ≤ normalizer ((center K).map (N.subtype.comp K.subtype) : Set G) ∧
      N ≤ normalizer ((center U).map ((N.subtype.comp K.subtype).comp U.subtype) : Set G) := by
  intro N K U
  let : U.Characteristic := omega₁_characteristic K
  let D := (center U).map U.subtype
  let : D.Characteristic := characteristic_of_characteristic_of_characteristic
  let ZK := (center K).map K.subtype
  let ZU := D.map K.subtype
  let : ZK.Normal := ConjAct.normal_of_characteristic_of_normal
  let : ZU.Normal := ConjAct.normal_of_characteristic_of_normal
  constructor
  · have hh := le_normalizer_map (H := ZK) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, ZK, map_map] using hh
  · have hh := le_normalizer_map (H := ZU) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, ZU, D, map_map,
      MonoidHom.comp_assoc] using hh

/-- The central four-group has no nonidentity Q-fixed element, and the
omega center has precisely two Q-fixed elements. Both centralizers use the
actual ambient image of the supplied Q. -/
public theorem normalizer_three_center_fixed_cards (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let A := (Q : Subgroup N).map N.subtype
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    ZK ⊓ centralizer (A : Set G) = ⊥ ∧
      Nat.card (ZU ⊓ centralizer (A : Set G) : Subgroup G) = 2 := by
  intro N K U A ZK ZU
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAcard : Nat.card A = 3 :=
    (card_map_of_injective N.subtype_injective).trans (d.normalizer_three_card h hN hproper Q)
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hAN : A ≤ N := map_subtype_le _
  have hZK : Nat.card ZK = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order h hN hproper).2.2.2
  have hZU : Nat.card ZU = 8 :=
    (card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
      U.subtype_injective)).trans (d.normalizer_core_omega_structure h hN hproper).2.1
  have hzK : z ∈ ZK := d.z_mem_normalizer_core_center
  have hzU : z ∈ ZU := d.normalizer_core_omega_inclusions.2.1 hzK
  have hne (B : Subgroup G) (hzB : z ∈ B) :
      Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) ≠ Nat.card B := by
    intro hc
    have heq := eq_of_le_of_card_ge (show B ⊓ centralizer (A : Set G) ≤ B from inf_le_left) hc.ge
    apply d.normalizer_three_not_centralizes h hN hproper Q
    intro a ha
    exact mem_centralizer_singleton_iff.mpr ((heq.symm ▸ hzB).2 a ha)
  constructor
  · apply eq_bot_of_card_eq
    have hmod := A.card_modEq_card_inf_centralizer ZK hA
      (hAN.trans d.normalizer_core_centers_normalized.1)
    have hd : Nat.card (ZK ⊓ centralizer (A : Set G) : Subgroup G) ∣ 2 ^ 2 := by
      simpa only [hZK, show 2 ^ 2 = (4 : ℕ) from rfl] using card_dvd_of_le (show ZK ⊓ centralizer (A : Set G) ≤ ZK from inf_le_left)
    obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hnot := hne ZK hzK
    rw [hZK, hc] at hmod hnot
    change 4 % 3 = 2 ^ n % 3 at hmod
    rw [hc]
    interval_cases n <;> norm_num at *
  · have hmod := A.card_modEq_card_inf_centralizer ZU hA
      (hAN.trans d.normalizer_core_centers_normalized.2)
    have hd : Nat.card (ZU ⊓ centralizer (A : Set G) : Subgroup G) ∣ 2 ^ 3 := by
      simpa only [hZU, show 2 ^ 3 = (8 : ℕ) from rfl] using card_dvd_of_le (show ZU ⊓ centralizer (A : Set G) ≤ ZU from inf_le_left)
    obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hnot := hne ZU hzU
    rw [hZU, hc] at hmod hnot
    change 8 % 3 = 2 ^ n % 3 at hmod
    rw [hc]
    interval_cases n <;> norm_num at *

/-- Choose the second central generator using an element of the supplied Q,
not merely an unspecified conjugator in N. -/
public theorem exists_normalizer_three_center_generator (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∃ t : G, t ∈ E ⊓ d.F ∧ t ∉ zpowers z ∧ orderOf t = 2 ∧
      (∃ q : Q, ((q : N) : G) * z * ((q : N) : G)⁻¹ = t) ∧
      (center K).map (N.subtype.comp K.subtype) = zpowers z ⊔ zpowers t := by
  classical
  intro H J E N K
  have hmove : ∃ q : Q, ((q : N) : G) * z * ((q : N) : G)⁻¹ ≠ z := by
    by_contra! hh
    apply d.normalizer_three_not_centralizes h hN hproper Q
    rintro x ⟨q, hq, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hh ⟨q, hq⟩))
  obtain ⟨q, hq⟩ := hmove
  let t := ((q : N) : G) * z * ((q : N) : G)⁻¹
  let Z := (center K).map (N.subtype.comp K.subtype)
  have hzZ : z ∈ Z := d.z_mem_normalizer_core_center
  have htZ : t ∈ Z :=
    (mem_normalizer_iff.mp (d.normalizer_core_centers_normalized.1 (q : N).property) z).mp hzZ
  have htE : t ∈ E ⊓ d.F := d.normalizer_core_center_le_inf h hN hproper htZ
  have ht2 : orderOf t = 2 := by
    exact (orderOf_injective (MulAut.conj ((q : N) : G)).toMonoidHom
      (MulAut.conj ((q : N) : G)).injective z).trans h.involution
  have ht1 : t ≠ 1 := by intro hh; simp [hh] at ht2
  have htz : t ∉ zpowers z := by
    intro ht
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at ht
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp ht
    have hnlt := Finset.mem_range.mp hn
    interval_cases n
    · exact ht1 (by simpa using heq.symm)
    · exact hq (by simpa [t] using heq.symm)
  refine ⟨t, htE, htz, ht2, ⟨q, rfl⟩, ?_⟩
  apply (eq_of_le_of_card_ge
    (sup_le (zpowers_le.mpr hzZ) (zpowers_le.mpr htZ)) ?_).symm
  have hZcard : Nat.card Z = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order h hN hproper).2.2.2
  have hpair := parrott_derived_pair_card z h t htE.1 htz
  rw [show ({z, t} : Set G) = {z} ∪ {t} from rfl, Subgroup.closure_union,
    ← zpowers_eq_closure, ← zpowers_eq_closure] at hpair
  exact hZcard.le.trans hpair.ge

/-- A point centralized by Q cannot be conjugate to z: its centralizer has
a factor three, whereas the original centralizer has order 10240. -/
public theorem normalizer_three_fixed_not_isConj (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G)
    (hv : v ∈ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G)) : ¬ IsConj z v := by
  intro hconj
  let N := normalizer (d.F : Set G)
  let A := (Q : Subgroup N).map N.subtype
  have hle : A ≤ centralizer ({v} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hv a ha)
  have hd := card_dvd_of_le hle
  rw [card_map_of_injective N.subtype_injective,
    d.normalizer_three_card h hN hproper Q] at hd
  obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
  let e := MulAut.conj g
  let f : centralizer ({z} : Set G) ≃ centralizer ({e z} : Set G) := {
    toFun a := ⟨e a, by
      rw [mem_centralizer_singleton_iff]
      simpa only [map_mul] using
        congrArg e (mem_centralizer_singleton_iff.mp a.property)⟩
    invFun a := ⟨e.symm a, by
      rw [mem_centralizer_singleton_iff]
      apply e.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using
        mem_centralizer_singleton_iff.mp a.property⟩
    left_inv a := Subtype.ext (e.symm_apply_apply a)
    right_inv a := Subtype.ext (e.apply_symm_apply a) }
  have hc := (Nat.card_congr f).symm.trans (h.card_and_solvable z).1
  change Nat.card (centralizer ({g * z * g⁻¹} : Set G)) = 10240 at hc
  rw [hc] at hd
  norm_num at hd

/-- Compatible generators for the two actual centers, for any supplied
Sylow three-subgroup. The third generator is exactly the fixed line of Q
and is not conjugate to the original involution. -/
public theorem exists_normalizer_three_center_generators (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let A := (Q : Subgroup N).map N.subtype
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    ∃ t v : G, t ∈ E ⊓ d.F ∧ v ∈ E ⊓ d.F ∧
      orderOf t = 2 ∧ orderOf v = 2 ∧ t ∉ zpowers z ∧ v ∉ ZK ∧
      ZK = zpowers z ⊔ zpowers t ∧ ZU = (zpowers z ⊔ zpowers t) ⊔ zpowers v ∧
      (∃ q : Q, ((q : N) : G) * z * ((q : N) : G)⁻¹ = t) ∧
      v ∈ centralizer (A : Set G) ∧ ZU ⊓ centralizer (A : Set G) = zpowers v ∧
      ¬ IsConj z v := by
  intro H J E N K U A ZK ZU
  let C := ZU ⊓ centralizer (A : Set G)
  obtain ⟨hKfix, hCcard⟩ := d.normalizer_three_center_fixed_cards h hN hproper Q
  change Nat.card C = 2 at hCcard
  obtain ⟨v, hvC, hv1⟩ : ∃ v : G, v ∈ C ∧ v ≠ 1 := by
    rcases C.bot_or_exists_ne_one with heq | hex
    · rw [heq, card_bot] at hCcard
      norm_num at hCcard
    · exact hex
  have hvEF : v ∈ E ⊓ d.F :=
    (d.normalizer_core_omega_structure h hN hproper).2.2.1 hvC.1
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hvpow : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hvEF.2
  have hv2 : orderOf v = 2 := orderOf_eq_prime hvpow hv1
  have hvout : v ∉ ZK := by
    intro hvK
    have hh : v ∈ ZK ⊓ centralizer (A : Set G) := ⟨hvK, hvC.2⟩
    rw [hKfix] at hh
    exact hv1 hh
  have hC : C = zpowers v := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr hvC) ?_).symm
    rw [Nat.card_zpowers, hv2, hCcard]
  have hZKcard : Nat.card ZK = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order h hN hproper).2.2.2
  have hZUcard : Nat.card ZU = 8 :=
    (card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
      U.subtype_injective)).trans (d.normalizer_core_omega_structure h hN hproper).2.1
  have hvN : v ∈ N := d.sylow_le_normalizer (d.le_sylow hvEF.2)
  have hjoin : ZU = ZK ⊔ zpowers v := by
    apply (eq_of_le_of_card_ge
      (sup_le d.normalizer_core_omega_inclusions.2.1 (zpowers_le.mpr hvC.1)) ?_).symm
    rw [card_sup_zpowers_of_normalizing_involution ZK v hvpow hvout
      (d.normalizer_core_centers_normalized.1 hvN), hZKcard, hZUcard]
  obtain ⟨t, ht, htz, ht2, hq, hZK⟩ :=
    d.exists_normalizer_three_center_generator h hN hproper Q
  refine ⟨t, v, ht, hvEF, ht2, hv2, htz, hvout, hZK, ?_, hq, hvC.2, hC,
    d.normalizer_three_fixed_not_isConj h hN hproper Q v hvC.2⟩
  exact hjoin.trans (congrArg (fun B : Subgroup G => B ⊔ zpowers v) hZK)

end Stellmacher.Recognition.ParrottSecondElementaryData
