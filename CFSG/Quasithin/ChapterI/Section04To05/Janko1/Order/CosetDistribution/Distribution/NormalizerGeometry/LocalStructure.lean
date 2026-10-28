module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry

/-!
# Cyclic six-subgroups and three-centralizers in Bender's normalizer

A subgroup of order six intersects the normal elementary Sylow subgroup in
order two. Its involution is consequently central, and multiplying it by an
element of order three produces a generator of order six.

For a subgroup X of order three, the action on the Sylow eight-group gives
an even fixed subgroup. The supplied ambient three-centralizer order and
normalizer order bound the relative centralizer by six; divisibility by both
two and three gives equality. Its intersection with the Sylow subgroup has
order two, the fixed-point input for the later seven-subgroup census.

Source: Bender, *Finite groups with large subgroups* (1974), §4, printed
pp.226–227. All conclusions use the actual subgroups and conjugation action.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

public theorem bender_six_cyclic (S : Subgroup G)
    (hSH : S ≤ normalizer (h.sylow : Set G)) (hS : Nat.card S = 6) : IsCyclic S := by
  classical
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by rw [hS]; decide)
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 (by rw [hS]; decide)
  have htG : orderOf (t : G) = 2 :=
    (orderOf_injective S.subtype S.subtype_injective t).trans ht
  have htQ := h.normalizer_involution_mem_sylow t htG (hSH t.property)
  let I := S ⊓ (h.sylow : Subgroup G)
  have hzle : zpowers (t : G) ≤ I := zpowers_le.mpr ⟨t.property, htQ⟩
  have hI : Nat.card I = 2 := by
    apply Nat.dvd_antisymm
    · have hd := Nat.dvd_gcd (card_dvd_of_le (show I ≤ S from inf_le_left))
        (card_dvd_of_le (show I ≤ (h.sylow : Subgroup G) from inf_le_right))
      simpa [hS, h.sylow_card] using hd
    · simpa [Nat.card_zpowers, htG] using card_dvd_of_le hzle
  have hIz : I = zpowers (t : G) := (eq_of_le_of_card_ge hzle (by
    rw [hI, Nat.card_zpowers, htG])).symm
  have hconjI : (x : G) * t * (x : G)⁻¹ ∈ I :=
    ⟨S.mul_mem (S.mul_mem x.property t.property) (S.inv_mem x.property),
      (mem_normalizer_iff.mp (hSH x.property) _).mp htQ⟩
  have hconjNe : (x : G) * t * (x : G)⁻¹ ≠ 1 := by
    intro he
    have ht1 : (t : G) = 1 := (MulAut.conj (x : G)).injective (he.trans (map_one _).symm)
    rw [ht1, orderOf_one] at htG
    omega
  rw [hIz, mem_zpowers_iff_mem_range_orderOf, htG] at hconjI
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hconjI
  have hnlt := Finset.mem_range.mp hn
  have hfix : (x : G) * t * (x : G)⁻¹ = t := by
    interval_cases n
    · exact (hconjNe (by simpa using he.symm)).elim
    · simpa using he.symm
  have hcomm : Commute x t := Subtype.ext (mul_inv_eq_iff_eq_mul.mp hfix)
  apply isCyclic_of_orderOf_eq_card (x * t)
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, ht]; decide), hx, ht, hS]

public theorem bender_three_centralizer {d : ℕ} (localData : BenderPrimeData G d)
    (normalizerData : BenderNormalizerData h)
    (X : Subgroup G) (hXH : X ≤ normalizer (h.sylow : Set G)) (hX : Nat.card X = 3) :
    Nat.card (normalizer (h.sylow : Set G) ⊓ centralizer (X : Set G) : Subgroup G) = 6 := by
  let H := normalizer (h.sylow : Set G)
  let C := H ⊓ centralizer (X : Set G)
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hX])
  have hxG : orderOf (x : G) = 3 :=
    (orderOf_injective X.subtype X.subtype_injective x).trans hx
  have hCdiv : Nat.card C ∣ 6 := by
    have hc := card_dvd_of_le (show C ≤ centralizer ({(x : G)} : Set G) from
      inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr x.property)))
    have hd := Nat.dvd_gcd (card_dvd_of_le (show C ≤ H from inf_le_left)) hc
    change Nat.card C ∣ Nat.gcd (Nat.card H) _ at hd
    rw [normalizerData.normalizer_card, localData.centralizer_three _ hxG] at hd
    rcases localData.d_cases with he | he <;> simp [he] at hd <;> exact hd
  have hthree : 3 ∣ Nat.card C := by
    let _ : IsCyclic X := isCyclic_of_prime_card hX
    have hle : X ≤ C := le_inf hXH (Subgroup.le_centralizer X)
    simpa [hX] using card_dvd_of_le hle
  let f : X →* MulAut h.sylow :=
    (h.sylow : Subgroup G).normalizerMonoidHom.comp (Subgroup.inclusion hXH)
  let _ : MulDistribMulAction X h.sylow := MulDistribMulAction.compHom h.sylow f
  let F := FixedPoints.subgroup X h.sylow
  have hmod := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hX)).card_modEq_card_fixedPoints h.sylow
  change Nat.card h.sylow % 3 = Nat.card F % 3 at hmod
  rw [h.sylow_card] at hmod
  have hFdiv : Nat.card F ∣ 8 := h.sylow_card ▸ F.card_subgroup_dvd_card
  have htwoF : 2 ∣ Nat.card F := by
    have hm := Nat.mem_divisors.mpr ⟨hFdiv, by decide⟩
    have he : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
    rw [he] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  have hFC : F.map (h.sylow : Subgroup G).subtype ≤ C := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨le_normalizer v.property, mem_centralizer_iff.mpr ?_⟩
    intro a ha
    have he := congrArg Subtype.val (hv (⟨a, ha⟩ : X))
    change a * (v : G) * a⁻¹ = v at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have htwo : 2 ∣ Nat.card C := by
    apply htwoF.trans
    have hd := card_dvd_of_le hFC
    rwa [card_map_of_injective (h.sylow : Subgroup G).subtype_injective] at hd
  apply Nat.dvd_antisymm hCdiv
  exact (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree

public theorem bender_sylow_three_centralizer_card {d : ℕ} (localData : BenderPrimeData G d)
    (normalizerData : BenderNormalizerData h)
    (X : Subgroup G) (hXH : X ≤ normalizer (h.sylow : Set G)) (hX : Nat.card X = 3) :
    Nat.card ((h.sylow : Subgroup G) ⊓ centralizer (X : Set G) : Subgroup G) = 2 := by
  let C := normalizer (h.sylow : Set G) ⊓ centralizer (X : Set G)
  let D := (h.sylow : Subgroup G) ⊓ centralizer (X : Set G)
  have hC : Nat.card C = 6 := h.bender_three_centralizer localData normalizerData X hXH hX
  have hDC : D ≤ C := inf_le_inf_right _ le_normalizer
  have hDdiv : Nat.card D ∣ 2 := by
    have hd := Nat.dvd_gcd (card_dvd_of_le (show D ≤ (h.sylow : Subgroup G) from inf_le_left))
      (card_dvd_of_le hDC)
    simpa [h.sylow_card, hC] using hd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [hC]; decide)
  have htG : orderOf (t : G) = 2 :=
    (orderOf_injective C.subtype C.subtype_injective t).trans ht
  have htD : (t : G) ∈ D :=
    ⟨h.normalizer_involution_mem_sylow t htG t.property.1, t.property.2⟩
  apply Nat.dvd_antisymm hDdiv
  have hd := card_dvd_of_le (zpowers_le.mpr htD)
  simpa [Nat.card_zpowers, htG] using hd

end CFSG.Quasithin.Janko1CentralizerData
