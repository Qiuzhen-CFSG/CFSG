module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveTypes
public import Theory.GroupTheory.PrimeOrderSylowArithmetic

/-!
# The preliminary seven-normalizer ratio in 47.3

The ambient order, the involution centralizer orders, and the two five-local
normalizer types imply |N_G(S):S| = 6 or 27 for a Sylow seven-subgroup S.
This is the ratio used to exclude a factor seven from C_G(X); it does not
use the incompatible order-21 assertion printed as 47.4.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3 proof, p.262.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem seven_not_dvd_five_normalizer
    (hFive : FiveNormalizerTypes G) (A : Subgroup G) (hA : Nat.card A = 5) :
    ¬ 7 ∣ Nat.card (normalizer (A : Set G)) := by
  rcases hFive A hA with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card (α := DihedralGroup 5), DihedralGroup.card]
    norm_num [Nat.factorial]
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_prod,
      Nat.card_eq_fintype_card (α := DihedralGroup 5), DihedralGroup.card]
    norm_num

/-- The two five-normalizer alternatives exclude an element of order five
from the centralizer of a Sylow seven-subgroup. -/
theorem seven_centralizer_not_five (hFive : FiveNormalizerTypes G)
    (P : Sylow 7 G) (hP : Nat.card P = 7) :
    ¬ 5 ∣ Nat.card (centralizer (P : Set G)) := by
  intro hd
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 hd
  let A := zpowers (x : G)
  have hA : Nat.card A = 5 := by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hle : (P : Subgroup G) ≤ normalizer (A : Set G) := by
    apply le_trans _ (centralizer_le_normalizer _)
    intro p hp
    rw [mem_centralizer_iff]
    intro a ha
    have hcomm : (x : G) * p = p * x := (x.property p hp).symm
    have he : zpowers (x : G) ≤ centralizer ({p} : Set G) := by
      apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr hcomm
    exact mem_centralizer_singleton_iff.mp (he ha)
  exact seven_not_dvd_five_normalizer hFive A hA (hP ▸ card_dvd_of_le hle)

/-- The preliminary ratio is forced independently of the later seven-local claim. -/
theorem seven_normalizer_ratio (hG : Nat.card G = 604800)
    (hInv : ∀ t : G, orderOf t = 2 →
      Nat.card (centralizer ({t} : Set G)) = 1920 ∨
      Nat.card (centralizer ({t} : Set G)) = 240)
    (hFive : FiveNormalizerTypes G) (P : Sylow 7 G) :
    Nat.card (normalizer (P : Set G)) / 7 = 6 ∨
      Nat.card (normalizer (P : Set G)) / 7 = 27 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hP : Nat.card P = 7 := P.card_eq_prime_of_dvd_of_not_sq_dvd
    (by rw [hG]; norm_num) (by rw [hG]; norm_num)
  let C := centralizer (P : Set G)
  let N := normalizer (P : Set G)
  have h2 : ¬ 2 ∣ Nat.card C := P.not_two_dvd_centralizer_card hP (by
    intro t ht
    rcases hInv t ht with h | h <;> rw [h] <;> norm_num)
  have h5 : ¬ 5 ∣ Nat.card C := seven_centralizer_not_five hFive P hP
  have hc : (Nat.card C).Coprime (2 ^ 7 * 5 ^ 2) :=
    (Nat.prime_two.coprime_pow_of_not_dvd h2).mul_right
      ((by decide : Nat.Prime 5).coprime_pow_of_not_dvd h5)
  have hcdiv : Nat.card C ∣ 189 := by
    apply hc.dvd_of_dvd_mul_left
    have hd := C.card_subgroup_dvd_card
    rw [hG] at hd
    convert hd using 1
    norm_num
  have ha : (C.subgroupOf N).index ∣ 6 :=
    P.centralizer_relIndex_normalizer_dvd_prime_sub_one hP
  have hn : Nat.card N ∣ 1134 := by
    have he := (C.subgroupOf N).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer _)).toEquiv] at he
    rw [← he]
    exact Nat.mul_dvd_mul hcdiv ha
  have hn378 : Nat.card N ∣ 378 := by
    have hd := Nat.dvd_gcd N.card_subgroup_dvd_card hn
    rw [hG] at hd
    norm_num at hd
    exact hd
  have hpN : 7 ∣ Nat.card N := by
    have hd := card_dvd_of_le (show (P : Subgroup G) ≤ N from le_normalizer)
    rwa [hP] at hd
  obtain ⟨n, hn7⟩ := hpN
  have hn54 : n ∣ 54 := by
    rw [hn7] at hn378
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 7)).mp hn378
  have hm := P.card_div_prime_modEq_of_normalizer_card hn7
  rw [hG] at hm
  have hm' : n % 7 = 6 := by simpa [Nat.ModEq] using hm.symm
  have hnsmall : n ≤ 54 := Nat.le_of_dvd (by decide) hn54
  have arith : ∀ n : Fin 55, n.val ∣ 54 → n.val % 7 = 6 → n.val = 6 ∨ n.val = 27 := by
    decide
  have he := arith ⟨n, by omega⟩ hn54 hm'
  change Nat.card N / 7 = 6 ∨ Nat.card N / 7 = 27
  rw [hn7]
  simpa using he

/-- At the source order a seven-normalizer of order 21 violates Sylow's congruence. -/
theorem seven_normalizer_ne_twenty_one (hG : Nat.card G = 604800) (P : Sylow 7 G) :
    Nat.card (normalizer (P : Set G)) ≠ 21 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro h
  have hm := P.card_div_prime_modEq_of_normalizer_card (m := 3) h
  rw [hG] at hm
  norm_num [Nat.ModEq] at hm

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
