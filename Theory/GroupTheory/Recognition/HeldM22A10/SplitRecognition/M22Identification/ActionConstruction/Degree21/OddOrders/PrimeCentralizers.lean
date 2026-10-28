module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.LocalClasses
public import Mathlib.GroupTheory.Transfer

/-!
# Prime centralizers from local data and Sylow arithmetic

For elements of orders seven and eleven, the even spectrum and the order-36
three-centralizers exclude factors two and three from their centralizers.
Their centralizer orders therefore divide 385. The action of a cyclic Sylow
p-subgroup's normalizer has order dividing p−1. Simplicity and Burnside transfer
exclude a trivial action. Sylow's congruence now forces eleven-centralizers
to have order eleven.

A subgroup of order 21 has a unique Sylow seven-subgroup. Thus its image
normalizes an ambient Sylow seven-subgroup, and every such normalizer has
order divisible by three. This excludes the remaining centralizer order 35;
seven-centralizers have order seven. The explicit three-centralizer premise
is supplied by `ThreeCentralizer` in the odd-spectrum assembly.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemmas 8–9 and Section 7, pp.15–16,
DOI 10.1016/0021-8693(68)90002-1. These deductions establish the odd-order
exclusions used in the table without presupposing that table or its character.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.OddOrders
open LocalModelDichotomy CaseII
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem prime_centralizer_dvd (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520)
    (h3 : ∀ y : G, orderOf y = 3 → Nat.card (centralizer ({y} : Set G)) = 36)
    {p : ℕ} (hp : p = 7 ∨ p = 11) (x : G) (hx : orderOf x = p) :
    Nat.card (centralizer ({x} : Set G)) ∣ 385 := by
  let C := centralizer ({x} : Set G)
  have h2 : ¬ 2 ∣ Nat.card C := by
    intro hd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hd
    have hyG : orderOf (y : G) = 2 := by simpa only [orderOf_coe] using hy
    have hc : Commute x (y : G) := (mem_centralizer_singleton_iff.mp y.property).symm
    have hm : orderOf (x * (y : G)) = p * 2 := by
      rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime, hx, hyG]
      rw [hx, hyG]
      rcases hp with rfl | rfl <;> decide
    have hs := even_orders D k L (x * (y : G)) (by rw [hm]; exact even_iff_two_dvd.mpr (dvd_mul_left 2 _))
    rcases hp with rfl | rfl <;> norm_num [hm] at hs
  have hn3 : ¬ 3 ∣ Nat.card C := by
    intro hd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hd
    have hyG : orderOf (y : G) = 3 := by simpa only [orderOf_coe] using hy
    have hxy : x ∈ centralizer ({(y : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp y.property).symm
    have hd := Subgroup.orderOf_dvd_natCard _ hxy
    rw [hx, h3 y hyG] at hd
    rcases hp with rfl | rfl <;> norm_num at hd
  have hc2 : (Nat.card C).Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
  have hc3 : (Nat.card C).Coprime 3 := ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr hn3).symm
  have hcop : (Nat.card C).Coprime (2 ^ 7 * 3 ^ 2) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨hc2.pow_right 7, hc3.pow_right 2⟩
  apply hcop.dvd_of_dvd_mul_left
  norm_num only [Nat.reducePow, Nat.reduceMul]
  exact hcard ▸ C.card_subgroup_dvd_card

private theorem prime_normalizer_arithmetic [IsSimpleGroup G]
    (hcard : Nat.card G = 443520) {p : ℕ} (hp : p = 7 ∨ p = 11)
    (x : G) (hx : orderOf x = p) :
    ∃ r : ℕ, r ∣ p - 1 ∧ r ≠ 1 ∧
      Nat.card (centralizer ({x} : Set G)) * r = Nat.card (normalizer (zpowers x : Set G)) ∧
      (443520 / (Nat.card (centralizer ({x} : Set G)) * r)) % p = 1 := by
  let : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  let P := zpowers x
  let N := normalizer (P : Set G)
  let f := P.normalizerMonoidHom
  have hP : Nat.card P = p := (Nat.card_zpowers x).trans hx
  have hker : Nat.card f.ker = Nat.card (centralizer ({x} : Set G)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set G))).toEquiv]
    simp only [P, zpowers_eq_closure, centralizer_closure]
  have hrange : Nat.card f.range ∣ p - 1 := by
    have hh := f.range.card_subgroup_dvd_card
    rwa [IsCyclic.card_mulAut, hP, Nat.totient_prime Fact.out] at hh
  have hN : Nat.card (centralizer ({x} : Set G)) * Nat.card f.range = Nat.card N := by
    simpa only [index_ker, hker] using f.ker.card_mul_index
  have hpi : ¬ p ∣ P.index := by
    have hh := P.card_mul_index
    rw [hP, hcard] at hh
    rcases hp with rfl | rfl <;> omega
  let S : Sylow p G := (IsPGroup.of_card (hP.trans (pow_one p).symm)).toSylow hpi
  have hm := card_sylow_modEq_one p G
  rw [S.card_eq_index_normalizer] at hm
  change N.index % p = 1 % p at hm
  have hne : Nat.card f.range ≠ 1 := by
    intro hr
    have hNC : normalizer (P : Set G) ≤ centralizer (P : Set G) := by
      apply (eq_of_le_of_card_ge (centralizer_le_normalizer (P : Set G)) ?_).ge
      simpa only [N, P, zpowers_eq_closure, centralizer_closure, hr, mul_one] using hN.ge
    have hc := MonoidHom.ker_transferSylow_isComplement' S hNC
    have hprod := hc.card_mul_card
    change Nat.card (MonoidHom.transferSylow S hNC).ker * Nat.card P = Nat.card G at hprod
    rw [hP, hcard] at hprod
    rcases (inferInstance : (MonoidHom.transferSylow S hNC).ker.Normal).eq_bot_or_eq_top with he | he
    · rw [he, card_bot] at hprod
      rcases hp with rfl | rfl <;> norm_num at hprod
    · rw [he, card_top, hcard] at hprod
      rcases hp with rfl | rfl <;> norm_num at hprod
  refine ⟨Nat.card f.range, hrange, hne, hN, ?_⟩
  rw [hN, ← hcard, ← N.card_mul_index]
  simp only [Nat.mul_div_cancel_left _ (Nat.card_pos (α := N))]
  rcases hp with rfl | rfl <;> exact hm

/-- Transfer and the Sylow congruence force the eleven-centralizer order. -/
public theorem eleven_centralizer_card [IsSimpleGroup G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520)
    (h3 : ∀ y : G, orderOf y = 3 → Nat.card (centralizer ({y} : Set G)) = 36)
    (x : G) (hx : orderOf x = 11) : Nat.card (centralizer ({x} : Set G)) = 11 := by
  have hd := prime_centralizer_dvd D k L hcard h3 (Or.inr rfl) x hx
  have h11 : 11 ∣ Nat.card (centralizer ({x} : Set G)) := by
    rw [← hx]
    exact Subgroup.orderOf_dvd_natCard _ (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨r, hr, hne, _, hm⟩ := prime_normalizer_arithmetic hcard (Or.inr rfl) x hx
  have hc := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  rw [show Nat.divisors 385 = {1, 5, 7, 11, 35, 55, 77, 385} by decide] at hc
  have hr' := Nat.mem_divisors.mpr ⟨hr, by decide⟩
  rw [show Nat.divisors (11 - 1) = {1, 2, 5, 10} by decide] at hr'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc hr'
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc <;>
    rcases hr' with rfl | rfl | rfl | rfl <;> simp_all

private theorem three_dvd_seven_normalizer
    (hcard : Nat.card G = 443520)
    (h21 : ∃ A : Subgroup G, Nat.card A = 21)
    (x : G) (hx : orderOf x = 7) :
    3 ∣ Nat.card (normalizer (zpowers x : Set G)) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨A, hA⟩ := h21
  let R : Sylow 7 A := Classical.choice inferInstance
  have hR : Nat.card R = 7 := by
    rw [R.card_eq_multiplicity, hA]
    decide +kernel
  have hiR : (R : Subgroup A).index = 3 := by
    have hh := (R : Subgroup A).card_mul_index
    rw [hR, hA] at hh
    omega
  have hcount : Nat.card (Sylow 7 A) = 1 := by
    have hd := R.card_dvd_index
    rw [hiR] at hd
    have hle := Nat.le_of_dvd (by decide : 0 < 3) hd
    have hm := card_sylow_modEq_one 7 A
    change Nat.card (Sylow 7 A) % 7 = 1 % 7 at hm
    omega
  let : Subsingleton (Sylow 7 A) := (Nat.card_eq_one_iff_unique.mp hcount).1
  let : (R : Subgroup A).Normal := R.normal_of_subsingleton
  let B := (R : Subgroup A).map A.subtype
  have hB : Nat.card B = 7 := (card_map_of_injective A.subtype_injective).trans hR
  have hAN : A ≤ normalizer (B : Set G) := by
    have hh := le_normalizer_map (H := (R : Subgroup A)) A.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hBi : ¬ 7 ∣ B.index := by
    have hh := B.card_mul_index
    rw [hB, hcard] at hh
    omega
  let S : Sylow 7 G := (IsPGroup.of_card (hB.trans (pow_one 7).symm)).toSylow hBi
  have hP : Nat.card (zpowers x) = 7 := (Nat.card_zpowers x).trans hx
  have hPi : ¬ 7 ∣ (zpowers x).index := by
    have hh := (zpowers x).card_mul_index
    rw [hP, hcard] at hh
    omega
  let T : Sylow 7 G := (IsPGroup.of_card (hP.trans (pow_one 7).symm)).toSylow hPi
  have hi : (normalizer (B : Set G)).index = (normalizer (zpowers x : Set G)).index :=
    S.card_eq_index_normalizer.symm.trans T.card_eq_index_normalizer
  have heq : Nat.card (normalizer (B : Set G)) =
      Nat.card (normalizer (zpowers x : Set G)) := by
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero (normalizer (zpowers x : Set G)).index_ne_zero_of_finite)
    calc
      _ = Nat.card G := by rw [← hi]; exact (normalizer (B : Set G)).card_mul_index
      _ = _ := (normalizer (zpowers x : Set G)).card_mul_index.symm
  have hd := card_dvd_of_le hAN
  rw [hA, heq] at hd
  exact dvd_trans (by decide : 3 ∣ 21) hd

/-- The supplied order-21 subgroup excludes the remaining mixed seven-centralizer. -/
public theorem seven_centralizer_card [IsSimpleGroup G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520)
    (h3 : ∀ y : G, orderOf y = 3 → Nat.card (centralizer ({y} : Set G)) = 36)
    (x : G) (hx : orderOf x = 7) : Nat.card (centralizer ({x} : Set G)) = 7 := by
  let C := centralizer ({x} : Set G)
  have hd := prime_centralizer_dvd D k L hcard h3 (Or.inl rfl) x hx
  have h7 : 7 ∣ Nat.card C := by
    rw [← hx]
    exact Subgroup.orderOf_dvd_natCard _ (mem_centralizer_singleton_iff.mpr rfl)
  have hnot11 : ¬ 11 ∣ Nat.card C := by
    let : Fact (Nat.Prime 11) := ⟨by decide⟩
    intro h
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 11 h
    have hyG : orderOf (y : G) = 11 := by simpa only [orderOf_coe] using hy
    have hxy : x ∈ centralizer ({(y : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp y.property).symm
    have hd := Subgroup.orderOf_dvd_natCard _ hxy
    rw [hx, eleven_centralizer_card D k L hcard h3 y hyG] at hd
    norm_num at hd
  have hc11 : (Nat.card C).Coprime 11 :=
    ((by decide : Nat.Prime 11).coprime_iff_not_dvd.mpr hnot11).symm
  have hd35 : Nat.card C ∣ 35 := hc11.dvd_of_dvd_mul_left hd
  have hc := Nat.mem_divisors.mpr ⟨hd35, by decide⟩
  rw [show Nat.divisors 35 = {1, 5, 7, 35} by decide] at hc
  have h3N := three_dvd_seven_normalizer hcard
    (by obtain ⟨A, hA, _⟩ := L.nonabelian_twenty_one; exact ⟨A, hA⟩) x hx
  obtain ⟨r, hr, _, hN, hm⟩ := prime_normalizer_arithmetic hcard (Or.inl rfl) x hx
  rw [← hN] at h3N
  have hr' := Nat.mem_divisors.mpr ⟨hr, by decide⟩
  rw [show Nat.divisors (7 - 1) = {1, 2, 3, 6} by decide] at hr'
  change Nat.card C = 7
  change 3 ∣ Nat.card C * r at h3N
  change 443520 / (Nat.card C * r) % 7 = 1 at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc hr'
  rcases hc with hc | hc | hc | hc <;>
    rcases hr' with rfl | rfl | rfl | rfl <;> simp_all


end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.OddOrders
