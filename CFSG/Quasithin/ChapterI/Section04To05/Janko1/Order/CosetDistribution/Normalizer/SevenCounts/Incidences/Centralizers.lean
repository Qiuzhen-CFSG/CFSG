module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Incidences.Counting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.FourCentralizers

/-!
# Centralizers for the seven-normalizer singleton count

The centralizer in H of an ambient involution has order dividing six:
its order divides both 6a and 120, and a is coprime to 120. In a singleton
fiber it has odd order, so a nontrivial centralizer is exactly a three-subgroup.
Conversely the order-six centralizer in H of a three-subgroup contains exactly
one involution, leaving 2d-2 external commuting involutions.

Source: Bender, *Finite groups with large subgroups* (1974), proof of (4.3),
printed p.226, the centralization count immediately before d = 3.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

private theorem divisors_six {n : ℕ} (hn : n ∣ 6) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
  have hc := Nat.mem_divisors.mpr ⟨hn, by decide⟩
  have hd : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
  rw [hd] at hc
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hc

omit [Finite G] in
/-- A singleton involution inverts only the identity in H. -/
public theorem bender_singleton_inverted_eq_one (H : Subgroup G) (u : G)
    (hu : orderOf u = 2) (huH : u ∉ H)
    (hf : Nat.card (BenderFiber H (benderRightCoset H u)) = 1)
    (x : G) (hxH : x ∈ H) (hx : u * x * u⁻¹ = x⁻¹) : x = 1 := by
  have hc : Nat.card (BenderInverted H u) = 1 :=
    (Nat.card_congr (benderFiberEquivInverted H u hu huH)).symm.trans hf
  have : Subsingleton (BenderInverted H u) := (Nat.card_eq_one_iff_unique.mp hc).1
  have he := Subsingleton.elim (α := BenderInverted H u) (⟨⟨x, hxH⟩, hx⟩ : BenderInverted H u)
    ⟨1, by simp⟩
  exact congrArg (fun v : BenderInverted H u => (v.1 : G)) he

namespace BenderSevenStructure
variable [IsSimpleGroup G] {h : Janko1CentralizerData G} {d : ℕ}
    (localData : BenderPrimeData G d) {S : Subgroup G} (hS : Nat.card S = 7)
    (structureData : BenderSevenStructure h S)
include h localData hS structureData

/-- The actual centralizer in H of any ambient involution has order dividing six. -/
public theorem involution_centralizer_dvd_six (u : G) (hu : orderOf u = 2) :
    Nat.card (normalizer (centralizer (S : Set G) : Set G) ⊓
      centralizer ({u} : Set G) : Subgroup G) ∣ 6 := by
  let C := normalizer (centralizer (S : Set G) : Set G) ⊓ centralizer ({u} : Set G)
  have hc120 : Nat.card C ∣ 120 := by
    have hd := card_dvd_of_le (show C ≤ centralizer ({u} : Set G) from inf_le_right)
    rwa [h.involution_centralizer_card u hu] at hd
  have hc6a : Nat.card C ∣ 6 * Nat.card (centralizer (S : Set G)) := by
    have hd := card_dvd_of_le
      (show C ≤ normalizer (centralizer (S : Set G) : Set G) from inf_le_left)
    rwa [structureData.normalizer_card localData hS] at hd
  exact ((h.seven_centralizer_coprime localData S hS).symm.of_dvd_left hc120).dvd_of_dvd_mul_right hc6a

/-- A centralized singleton has precisely a three-subgroup as its centralizer in H. -/
public theorem singleton_centralizer_card
    (u : BenderCentralizedSingletons (normalizer (centralizer (S : Set G) : Set G))) :
    Nat.card (normalizer (centralizer (S : Set G) : Set G) ⊓
      centralizer ({u.1} : Set G) : Subgroup G) = 3 := by
  let H := normalizer (centralizer (S : Set G) : Set G)
  let C := H ⊓ centralizer ({u.1} : Set G)
  have huH : u.1 ∉ H := fun he => u.2.2.1 ((benderRightCoset_eq_base_iff H _).mpr he)
  have hodd : ¬ 2 ∣ Nat.card C := by
    intro hd
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hd
    have hv2 : orderOf (v : G) = 2 := (orderOf_injective _ C.subtype_injective _).trans hv
    have hvi : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hv2).1)
    have he : u.1 * (v : G) * u.1⁻¹ = (v : G)⁻¹ := by
      rw [hvi]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp v.2.2).symm
    exact (orderOf_eq_prime_iff.mp hv2).2
      (bender_singleton_inverted_eq_one H u.1 u.2.1 huH u.2.2.2.1 v v.2.1 he)
  have hne : Nat.card C ≠ 1 := by
    intro hc
    have : Subsingleton C := (Nat.card_eq_one_iff_unique.mp hc).1
    obtain ⟨a, haH, ha1, hau⟩ := u.2.2.2.2
    exact ha1 (congrArg Subtype.val (Subsingleton.elim
      (⟨a, haH, mem_centralizer_singleton_iff.mpr hau.eq⟩ : C) 1))
  have hd := divisors_six (structureData.involution_centralizer_dvd_six localData hS u.1 u.2.1)
  change Nat.card C = 1 ∨ Nat.card C = 2 ∨ Nat.card C = 3 ∨ Nat.card C = 6 at hd
  rcases hd with hd | hd | hd | hd <;> omega

end BenderSevenStructure

/-- Exactly one involution of H centralizes an element of order three. -/
public theorem bender_seven_inside_commuting_three_card {S : Subgroup G}
    (geometry : BenderSevenGeometry S)
    (x : G) (hxH : x ∈ normalizer (centralizer (S : Set G) : Set G))
    (hx : orderOf x = 3) :
    Nat.card {u : G // orderOf u = 2 ∧ Commute u x ∧
      u ∈ normalizer (centralizer (S : Set G) : Set G)} = 1 := by
  classical
  let H := normalizer (centralizer (S : Set G) : Set G)
  let C := H ⊓ centralizer ({x} : Set G)
  have hc : Nat.card C = 6 := by
    have hc := geometry.three_centralizer (zpowers x) (zpowers_le.mpr hxH)
      ((Nat.card_zpowers x).trans hx)
    simpa only [zpowers_eq_closure, centralizer_closure] using hc
  let : IsCyclic C := geometry.six_cyclic C inf_le_left hc
  let : Fintype C := Fintype.ofFinite _
  have hcount : Nat.card {u : C // orderOf u = 2} = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hh := IsCyclic.card_orderOf_eq_totient (α := C) (d := 2)
      (by rw [← Nat.card_eq_fintype_card, hc]; decide)
    exact hh.trans (by decide)
  let e : {u : G // orderOf u = 2 ∧ Commute u x ∧ u ∈ H} ≃
      {u : C // orderOf u = 2} := {
    toFun := fun u => ⟨⟨u.1, u.2.2.2, mem_centralizer_singleton_iff.mpr u.2.2.1.eq⟩,
      (orderOf_injective _ C.subtype_injective _).symm.trans u.2.1⟩
    invFun := fun u => ⟨u.1, (orderOf_injective _ C.subtype_injective _).trans u.2,
      mem_centralizer_singleton_iff.mp u.1.2.2, u.1.2.1⟩
    left_inv := by intro u; rfl
    right_inv := by intro u; rfl }
  exact (Nat.card_congr e).trans hcount

/-- The ambient prime count leaves exactly 2d-2 external commuting involutions. -/
public theorem bender_seven_outside_commuting_three_card {d : ℕ}
    (localData : BenderPrimeData G d) {S : Subgroup G} (geometry : BenderSevenGeometry S)
    (x : G) (hxH : x ∈ normalizer (centralizer (S : Set G) : Set G))
    (hx : orderOf x = 3) :
    Nat.card {u : G // orderOf u = 2 ∧ Commute u x ∧
      u ∉ normalizer (centralizer (S : Set G) : Set G)} = 2 * (d - 1) := by
  classical
  let H := normalizer (centralizer (S : Set G) : Set G)
  let J := {u : G // orderOf u = 2 ∧ Commute u x}
  let p : J → Prop := fun u => u.1 ∈ H
  let ei : {u : J // p u} ≃ {u : G // orderOf u = 2 ∧ Commute u x ∧ u ∈ H} := {
    toFun := fun u => ⟨u.1.1, u.1.2.1, u.1.2.2, u.2⟩
    invFun := fun u => ⟨⟨u.1, u.2.1, u.2.2.1⟩, u.2.2.2⟩
    left_inv := by intro u; rfl
    right_inv := by intro u; rfl }
  let eo : {u : J // ¬ p u} ≃ {u : G // orderOf u = 2 ∧ Commute u x ∧ u ∉ H} := {
    toFun := fun u => ⟨u.1.1, u.1.2.1, u.1.2.2, u.2⟩
    invFun := fun u => ⟨⟨u.1, u.2.1, u.2.2.1⟩, u.2.2.2⟩
    left_inv := by intro u; rfl
    right_inv := by intro u; rfl }
  have hc := Nat.card_congr (Equiv.sumCompl p).symm
  rw [Nat.card_sum, Nat.card_congr ei, Nat.card_congr eo] at hc
  have hi := bender_seven_inside_commuting_three_card geometry x hxH hx
  change Nat.card {u : G // orderOf u = 2 ∧ Commute u x ∧ u ∈ H} = 1 at hi
  rw [hi] at hc
  have hj := localData.commuting_three x hx
  change Nat.card J = _ at hj
  change Nat.card {u : G // orderOf u = 2 ∧ Commute u x ∧ u ∉ H} = _
  rcases localData.d_cases with hd | hd <;> omega


private theorem three_centralizes_small_cyclic (K : Subgroup G) [IsCyclic K]
    (hK : Nat.card K ∣ 6) (x : G) (hx : orderOf x = 3)
    (hxK : x ∈ normalizer (K : Set G)) : ∀ a ∈ K, Commute x a := by
  let f : MulAut K := K.normalizerMonoidHom ⟨x, hxK⟩
  have hf3 : f ^ 3 = 1 := by
    change (K.normalizerMonoidHom ⟨x, hxK⟩) ^ 3 = 1
    rw [← map_pow, show (⟨x, hxK⟩ : normalizer (K : Set G)) ^ 3 = 1 from
      Subtype.ext (hx ▸ pow_orderOf_eq_one x), map_one]
  have hcop : Nat.Coprime (Nat.card (MulAut K)) 3 := by
    rw [IsCyclic.card_mulAut]
    rcases divisors_six hK with hk | hk | hk | hk <;> rw [hk] <;> decide
  have hf : f = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨pow_card_eq_one', hf3⟩
  intro a ha
  have he : x * a * x⁻¹ = a := congrArg (fun f : MulAut K => (f ⟨a, ha⟩ : G)) hf
  exact mul_inv_eq_iff_eq_mul.mp he

private theorem cyclic_six_three_mem_zpowers {D : Type*} [Group D] [Finite D] [IsCyclic D]
    (hD : Nat.card D = 6) (x y : D) (hx : orderOf x = 3) (hy : orderOf y = 3) :
    x ∈ zpowers y := by
  let _ : CommGroup D := IsCyclic.commGroup
  let T := (powMonoidHom 3 : D →* D).ker
  have hT : Nat.card T = 3 := by
    rw [IsCyclic.card_powMonoidHom_ker, hD]
    decide
  have hyT : zpowers y ≤ T := zpowers_le.mpr (by
    change y ^ 3 = 1
    exact hy ▸ pow_orderOf_eq_one y)
  have he : zpowers y = T := eq_of_le_of_card_ge hyT (by rw [Nat.card_zpowers, hy, hT])
  rw [he]
  change x ^ 3 = 1
  exact hx ▸ pow_orderOf_eq_one x

/-- An external involution centralizing a three-element of H has a singleton fiber.
The three-element normalizes the cyclic inversion set, hence centralizes it.
An even inversion set contradicts the order-eight common centralizer of a
four-group; an inversion set of order three contradicts cyclicity of C_H(x). -/
public theorem bender_seven_commuting_three_singleton [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {S : Subgroup G} (geometry : BenderSevenGeometry S)
    (x u : G) (hxH : x ∈ normalizer (centralizer (S : Set G) : Set G))
    (hx : orderOf x = 3) (hu : orderOf u = 2)
    (huH : u ∉ normalizer (centralizer (S : Set G) : Set G)) (hux : Commute u x) :
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G))
      (benderRightCoset (normalizer (centralizer (S : Set G) : Set G)) u)) = 1 := by
  let H := normalizer (centralizer (S : Set G) : Set G)
  obtain ⟨K, hK, hcyc, hdiv⟩ := geometry.inverted_subgroup u hu huH
  let : IsCyclic K := hcyc
  have hKH : K ≤ H := fun a ha => ((hK a).mp ha).1
  have hxK : x ∈ normalizer (K : Set G) := by
    let e := MulAut.conj x
    have heu : e u = u := mul_inv_eq_iff_eq_mul.mpr hux.symm.eq
    apply mem_normalizer_iff.mpr
    intro a
    change a ∈ K ↔ e a ∈ K
    rw [hK, hK]
    have hH : a ∈ H ↔ e a ∈ H := (mem_normalizer_iff.mp (le_normalizer hxH)) a
    have heq : u * e a * u⁻¹ = (e a)⁻¹ ↔ u * a * u⁻¹ = a⁻¹ := by
      calc
        _ ↔ e (u * a * u⁻¹) = e (a⁻¹) := by rw [map_mul, map_mul, map_inv, map_inv, heu]
        _ ↔ _ := e.injective.eq_iff
    exact and_congr hH heq.symm
  have hxcomm := three_centralizes_small_cyclic K hdiv x hx hxK
  have hnot2 : ¬ 2 ∣ Nat.card K := by
    intro hd
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 hd
    have hv2 : orderOf (v : G) = 2 := (orderOf_injective _ K.subtype_injective _).trans hv
    have hvi : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hv2).1)
    have huv : Commute u (v : G) := mul_inv_eq_iff_eq_mul.mp
      (((hK v).mp v.2).2.trans hvi)
    have hvnot : (v : G) ∉ zpowers u := by
      intro hvu
      have he : zpowers (v : G) = zpowers u := eq_of_le_of_card_ge
        (zpowers_le.mpr hvu) (by rw [Nat.card_zpowers, Nat.card_zpowers, hv2, hu])
      exact huH ((zpowers_le.mpr (hKH v.2)) (he.symm ▸ mem_zpowers u))
    have hc := h.common_centralizer_card_of_involutions u v hu huv
      (orderOf_eq_prime_iff.mp hv2).1 hvnot
    let C := centralizer ({u} : Set G) ⊓ centralizer ({(v : G)} : Set G)
    have hxC : x ∈ C := ⟨mem_centralizer_singleton_iff.mpr hux.symm.eq,
      mem_centralizer_singleton_iff.mpr (hxcomm v v.2).eq⟩
    have hd := orderOf_dvd_natCard (⟨x, hxC⟩ : C)
    rw [← orderOf_coe ⟨x, hxC⟩, hx, hc] at hd
    norm_num at hd
  have hnot3 : Nat.card K ≠ 3 := by
    intro hk3
    let D := H ⊓ centralizer ({x} : Set G)
    have hD : Nat.card D = 6 := by
      have hh := geometry.three_centralizer (zpowers x) (zpowers_le.mpr hxH)
        ((Nat.card_zpowers x).trans hx)
      simpa only [zpowers_eq_closure, centralizer_closure] using hh
    let : IsCyclic D := geometry.six_cyclic D inf_le_left hD
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 (by rw [hk3])
    have hv3 : orderOf (v : G) = 3 := (orderOf_injective _ K.subtype_injective _).trans hv
    have hvD : (v : G) ∈ D := ⟨hKH v.2,
      mem_centralizer_singleton_iff.mpr (hxcomm v v.2).symm.eq⟩
    have hxD : x ∈ D := ⟨hxH, mem_centralizer_singleton_iff.mpr rfl⟩
    have he := cyclic_six_three_mem_zpowers hD (⟨x, hxD⟩ : D) ⟨v, hvD⟩
      ((orderOf_injective _ D.subtype_injective _).symm.trans hx)
      ((orderOf_injective _ D.subtype_injective _).symm.trans hv3)
    have hxmem : x ∈ K := by
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp he
      have hnG := congrArg Subtype.val hn
      change (v : G) ^ n = x at hnG
      exact hnG ▸ K.zpow_mem v.2 n
    have hinv := ((hK x).mp hxmem).2
    have he : x = x⁻¹ := (mul_inv_eq_iff_eq_mul.mpr hux.eq).symm.trans hinv
    have hx2 : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ = x⁻¹ * x := congrArg (· * x) he
        _ = 1 := inv_mul_cancel x
    have hd := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at hd
    norm_num at hd
  have hk1 : Nat.card K = 1 := by
    rcases divisors_six hdiv with hh | hh | hh | hh <;> omega
  exact (bender_fiber_card_of_inverted_subgroup H u hu huH K hK).trans hk1

end CFSG.Quasithin.Janko1CentralizerData
