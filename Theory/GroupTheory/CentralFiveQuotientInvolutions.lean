module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Involutions modulo a central subgroup of order five

Taking fifth powers lifts involutions through an order-five kernel. If the
kernel is central, such lifts are unique, so full involution centralizers
also lift. A centralizer of order twenty and exponent dividing ten descends
to a four-group, identified by an actual equivalence with `DihedralGroup 2`.
Involution fusion descends through the same quotient projection.

These elementary arguments implement the quotient step of Aschbacher,
*Sporadic Groups* (1994), 47.2(2), printed p.261. They adapt the checked
central-five proofs in
`Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore.FiveCentralizer.Recognition`.
-/

public section

open Subgroup

namespace Theory.GroupTheory.CentralFiveQuotient

/-- The order formula for the image of a subgroup containing the kernel. -/
private theorem card_map_mul_kernel {A B : Type*} [Group A] [Group B]
    (f : A →* B) (U : Subgroup A) (hker : f.ker ≤ U) :
    Nat.card (U.map f) * Nat.card f.ker = Nat.card U := by
  have h := (f.ker.subgroupOf U).index_mul_card
  change f.ker.relIndex U * Nat.card (f.ker.subgroupOf U) = Nat.card U at h
  rw [relIndex_ker, Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv] at h
  exact h

private theorem central_fifth_power {A : Type*} [Group A]
    (K : Subgroup A) (hK : Nat.card K = 5) (x : A) (hx : x ∈ K) :
    x ^ 5 = 1 := by
  have hh := pow_card_eq_one' (x := (⟨x, hx⟩ : K))
  rw [hK] at hh
  exact congrArg Subtype.val hh

/-- Taking the fifth power lifts every quotient involution. Centrality is not needed. -/
theorem exists_involution_lift {A : Type*} [Group A]
    (K : Subgroup A) [K.Normal] (hK : Nat.card K = 5)
    (b : A ⧸ K) (hb : orderOf b = 2) :
    ∃ a : A, orderOf a = 2 ∧ QuotientGroup.mk' K a = b := by
  let q := QuotientGroup.mk' K
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective K b
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have ha2 : a ^ 2 ∈ K := (QuotientGroup.eq_one_iff _).mp (by
    change q (a ^ 2) = 1
    rw [map_pow, ha, hb2])
  have ha10 : a ^ 10 = 1 := by simpa only [← pow_mul] using central_fifth_power K hK (a ^ 2) ha2
  have ha5q : q (a ^ 5) = b := by
    rw [map_pow, ha, show 5 = 2 * 2 + 1 by rfl, pow_succ, pow_mul, hb2, one_pow, one_mul]
  refine ⟨a ^ 5, orderOf_eq_prime (by simpa only [← pow_mul] using ha10) ?_, ha5q⟩
  intro hh
  have hb1 : b = 1 := by rw [← ha5q, hh, map_one]
  simp [hb1] at hb

/-- Involutions with the same image modulo a central five-subgroup are equal. -/
theorem involution_eq_of_image_eq {A : Type*} [Group A]
    (K : Subgroup A) [K.Normal] (hKZ : K ≤ center A) (hK : Nat.card K = 5)
    (a b : A) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : QuotientGroup.mk' K a = QuotientGroup.mk' K b) : a = b := by
  let d := a / b
  have hdZ : d ∈ K := QuotientGroup.eq_iff_div_mem.mp hab
  have hd5 : d ^ 5 = 1 := central_fifth_power K hK d hdZ
  have hdb : Commute d b := (mem_center_iff.mp (hKZ hdZ) b).symm
  have habc : Commute a b := by
    simpa [d, div_eq_mul_inv, mul_assoc] using hdb.mul_left (Commute.refl b)
  have hd2 : d ^ 2 = 1 := by
    change (a / b) ^ 2 = 1
    rw [div_eq_mul_inv, (habc.inv_right).mul_pow, ha, inv_pow, hb]
    simp
  have hd1 : d = 1 := by
    have hh := hd5
    rw [show 5 = 2 * 2 + 1 by rfl, pow_succ, pow_mul, hd2, one_pow, one_mul] at hh
    exact hh
  exact div_eq_one.mp hd1

/-- The full centralizer of an involution is the inverse image of its quotient centralizer. -/
theorem centralizer_comap {A : Type*} [Group A]
    (K : Subgroup A) [K.Normal] (hKZ : K ≤ center A) (hK : Nat.card K = 5)
    (t : A) (ht : orderOf t = 2) :
    (centralizer ({QuotientGroup.mk' K t} : Set (A ⧸ K))).comap
      (QuotientGroup.mk' K) = centralizer ({t} : Set A) := by
  let q := QuotientGroup.mk' K
  ext a
  simp only [mem_comap, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hc : a * t * a⁻¹ = t := by
      apply involution_eq_of_image_eq K hKZ hK
      · change (MulAut.conj a t) ^ 2 = 1
        have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
        rw [← map_pow, ht2, map_one]
      · exact ht ▸ pow_orderOf_eq_one t
      · change q (a * t * a⁻¹) = q t
        rw [map_mul, map_mul, map_inv, h, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_inv_eq_iff_eq_mul.mp hc
  · intro h
    simpa only [map_mul] using congrArg q h

private theorem quotient_involution_data {A : Type*} [Group A] [Finite A]
    (K : Subgroup A) [K.Normal] (hKZ : K ≤ center A) (hK : Nat.card K = 5)
    (t : A) (ht : orderOf t = 2)
    (hc : Nat.card (centralizer ({t} : Set A)) = 20)
    (hp : ∀ x : centralizer ({t} : Set A), x ^ 10 = 1)
    (hf : ∀ x : A, orderOf x = 2 → IsConj x t) :
    orderOf (QuotientGroup.mk' K t) = 2 ∧
    Nat.card (centralizer ({QuotientGroup.mk' K t} : Set (A ⧸ K))) = 4 ∧
    (∀ x : centralizer ({QuotientGroup.mk' K t} : Set (A ⧸ K)), x ^ 2 = 1) ∧
    (∀ x : A ⧸ K, orderOf x = 2 → IsConj x (QuotientGroup.mk' K t)) := by
  let q := QuotientGroup.mk' K
  let C := centralizer ({t} : Set A)
  let B := centralizer ({q t} : Set (A ⧸ K))
  have hBC : B.comap q = C := centralizer_comap K hKZ hK t ht
  have hCB : C.map q = B := by
    rw [← hBC, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hker : q.ker ≤ C := by
    rw [QuotientGroup.ker_mk']
    exact hKZ.trans (center_le_centralizer _)
  have hBcard : Nat.card B = 4 := by
    have hh := card_map_mul_kernel q C hker
    rw [hCB, QuotientGroup.ker_mk', hK, hc] at hh
    omega
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htq2 : orderOf (q t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ht2, map_one]
    · intro heq
      have hh := involution_eq_of_image_eq K hKZ hK t 1 ht2 (by simp) (by
        simpa only [map_one] using heq)
      simp [hh] at ht
  refine ⟨htq2, hBcard, ?_, ?_⟩
  · intro x
    have hxB : (x : A ⧸ K) ∈ C.map q := by rw [hCB]; exact x.property
    obtain ⟨y, hy, hyx⟩ := mem_map.mp hxB
    have hx10 : x ^ 10 = 1 := by
      apply Subtype.ext
      change (x : A ⧸ K) ^ 10 = 1
      rw [← hyx, ← map_pow]
      have hh : y ^ 10 = 1 := congrArg Subtype.val (hp ⟨y, hy⟩)
      rw [hh, map_one]
    have hd4 : orderOf x ∣ 4 := by
      have hh := orderOf_dvd_natCard x
      change orderOf x ∣ Nat.card B at hh
      rwa [hBcard] at hh
    have hd10 := orderOf_dvd_of_pow_eq_one hx10
    exact orderOf_dvd_iff_pow_eq_one.mp (show orderOf x ∣ 2 from Nat.dvd_gcd hd4 hd10)
  · intro x hx
    obtain ⟨a, ha, haq⟩ := exists_involution_lift K hK x hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (hf a ha)
    refine isConj_iff.mpr ⟨q g, ?_⟩
    rw [← haq]
    simpa only [map_mul, map_inv] using congrArg q hg

/-- Fusion and a centralizer of order twenty and exponent dividing ten give
the full involution geometry in the literal quotient by the central five. -/
theorem involution_geometry {A : Type*} [Group A] [Finite A]
    (K : Subgroup A) [K.Normal] (hKZ : K ≤ center A) (hK : Nat.card K = 5)
    (t : A) (ht : orderOf t = 2)
    (hc : Nat.card (centralizer ({t} : Set A)) = 20)
    (hp : ∀ x : centralizer ({t} : Set A), x ^ 10 = 1)
    (hf : ∀ x : A, orderOf x = 2 → IsConj x t) :
    orderOf (QuotientGroup.mk' K t) = 2 ∧
      (∀ x : A ⧸ K, orderOf x = 2 → IsConj x (QuotientGroup.mk' K t)) ∧
      Nonempty (centralizer ({QuotientGroup.mk' K t} : Set (A ⧸ K)) ≃* DihedralGroup 2) := by
  obtain ⟨htq, hcard, hpow, hfusion⟩ := quotient_involution_data K hKZ hK t ht hc hp hf
  let B := centralizer ({QuotientGroup.mk' K t} : Set (A ⧸ K))
  have hbcard : Nat.card B = 4 := hcard
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by rw [hbcard]; decide)
  let : IsKleinFour B := ⟨hbcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
    (fun x hx => orderOf_eq_prime (hpow x) hx)⟩
  exact ⟨htq, hfusion, IsKleinFour.nonempty_mulEquiv⟩

end Theory.GroupTheory.CentralFiveQuotient
