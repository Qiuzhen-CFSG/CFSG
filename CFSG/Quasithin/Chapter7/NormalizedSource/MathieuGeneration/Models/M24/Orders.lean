module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.MixedCoverage
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.NumberTheory.Divisors

/-!
# Native M₂₄ Cartan orders

The centralizers of the five- and seven-parts of the actual native mixed-order
representatives bound odd abelian subgroups containing those primes. Permutation
centralizer orders and the native exclusion of a second factor of three give
orders 5 or 15, and 7 or 21, respectively.

Source: Aschbacher--Smith, Definition E.3.37 and Table 7.3.4,
printed pp.239 and 699. Used to exclude the native Mathieu Cartan witnesses.
-/

public section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24Cartan
open Subgroup Sporadic.Mathieu
open scoped IsMulCommutative

private theorem abelian_order_bounds (B : Subgroup M24) [IsMulCommutative B]
    (p : ℕ) [Fact p.Prime] (y : M24) (hy : orderOf y = p)
    (hpG : ¬ p * p ∣ Nat.card M24) (hpB : p ∣ Nat.card B) :
    Nat.card B ∣ Nat.card (centralizer ({y} : Set M24)) ∧
      Nat.card B ∣ Nat.card (centralizer ({y.val} : Set (Equiv.Perm (Fin 24)))) := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) p hpB
  obtain ⟨n, hn⟩ := IsConj.of_order_eq_prime_power_generator hy
    ((Subgroup.orderOf_coe x).trans hx) hpG
  obtain ⟨g, hg⟩ := isConj_iff.mp hn
  let e := MulAut.conj g
  let D := B.map e.toMonoidHom
  have ht : y ^ n ∈ D := hg ▸ Subgroup.mem_map_of_mem e.toMonoidHom x.property
  have htorder : orderOf (y ^ n) = p := by
    rw [← hg]
    exact (e.orderOf_eq x.val).trans ((Subgroup.orderOf_coe x).trans hx)
  let u : zpowers y := ⟨y ^ n, pow_mem (mem_zpowers y) n⟩
  have hu : u ≠ 1 := by
    intro hu
    have hone : y ^ n = 1 := congrArg Subtype.val hu
    rw [hone, orderOf_one] at htorder
    exact (Fact.out : Nat.Prime p).ne_one htorder.symm
  have hgen : (⟨y, mem_zpowers y⟩ : zpowers y) ∈ zpowers u :=
    mem_zpowers_of_prime_card ((Nat.card_zpowers y).trans hy) hu
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hgen
  have hyD : y ∈ D := by
    have he : (y ^ n) ^ j = y := congrArg Subtype.val hj
    exact he ▸ D.zpow_mem ht j
  let : IsMulCommutative D := inferInstance
  have hD : D ≤ centralizer ({y} : Set M24) := by
    intro d hd
    exact mem_centralizer_singleton_iff.mpr
      (setLike_mul_comm (s := D) hd hyD)
  have hcard : Nat.card D = Nat.card B := card_map_of_injective e.injective
  constructor
  · rw [← hcard]
    exact card_dvd_of_le hD
  · have hm : D.map M24.subtype ≤ centralizer ({y.val} : Set (Equiv.Perm (Fin 24))) := by
      rintro a ⟨d, hd, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hD hd)))
    have hd := card_dvd_of_le hm
    rwa [card_map_of_injective M24.subtype_injective, hcard] at hd

/-- An odd abelian subgroup containing a seven-element has order seven or twenty-one. -/
theorem abelian_seven_card (B : Subgroup M24) [IsMulCommutative B]
    (ho : Odd (Nat.card B)) (h7 : 7 ∣ Nat.card B) :
    Nat.card B = 7 ∨ Nat.card B = 21 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hy : orderOf (M24OddCyclic.representative 1 ^ 3) = 7 := by
    rw [orderOf_pow, M24OddCyclic.representative_order]
    decide
  obtain ⟨hC, hP⟩ := abelian_order_bounds B 7 _ hy (by rw [m24_order]; decide) h7
  have htype : ((M24OddCyclic.representative 1 ^ 3).val).cycleType = {7, 7, 7} := by
    change (M24OddCyclic.representativePerm 1 ^ 3).cycleType = _
    decide +kernel
  have hsym : Nat.card (centralizer
      ({(M24OddCyclic.representative 1 ^ 3).val} : Set (Equiv.Perm (Fin 24)))) = 12348 := by
    rw [Equiv.Perm.nat_card_centralizer]
    rw [htype]
    norm_num [Nat.factorial]
  rw [hsym] at hP
  have hdiv : Nat.card B ∣ 252 := by
    have h := Nat.dvd_gcd B.card_subgroup_dvd_card hP
    rwa [m24_order, show Nat.gcd 244823040 12348 = 252 by decide] at h
  have h9 : ¬ 9 ∣ Nat.card B := fun h =>
    M24OddCyclic.sevenPart_centralizer_not_nine (h.trans hC)
  have hcheck : ∀ n ∈ Nat.divisors 252, Odd n → 7 ∣ n → ¬ 9 ∣ n → n = 7 ∨ n = 21 := by
    decide +kernel
  exact hcheck _ (Nat.mem_divisors.mpr ⟨hdiv, by decide⟩) ho h7 h9

/-- An odd abelian subgroup containing a five-element has order five or fifteen. -/
theorem abelian_five_card (B : Subgroup M24) [IsMulCommutative B]
    (ho : Odd (Nat.card B)) (h5 : 5 ∣ Nat.card B) :
    Nat.card B = 5 ∨ Nat.card B = 15 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hy : orderOf (M24OddCyclic.representative 0 ^ 3) = 5 := by
    rw [orderOf_pow, M24OddCyclic.representative_order]
    decide
  obtain ⟨hC, hP⟩ := abelian_order_bounds B 5 _ hy (by rw [m24_order]; decide) h5
  have htype : ((M24OddCyclic.representative 0 ^ 3).val).cycleType = {5, 5, 5, 5} := by
    change (M24OddCyclic.representativePerm 0 ^ 3).cycleType = _
    decide +kernel
  have hsym : Nat.card (centralizer
      ({(M24OddCyclic.representative 0 ^ 3).val} : Set (Equiv.Perm (Fin 24)))) = 360000 := by
    rw [Equiv.Perm.nat_card_centralizer]
    rw [htype]
    norm_num [Nat.factorial]
  rw [hsym] at hP
  have hdiv : Nat.card B ∣ 2880 := by
    have h := Nat.dvd_gcd B.card_subgroup_dvd_card hP
    rwa [m24_order, show Nat.gcd 244823040 360000 = 2880 by decide] at h
  have h9 : ¬ 9 ∣ Nat.card B := fun h =>
    M24OddCyclic.fivePart_centralizer_not_nine (h.trans hC)
  have hcheck : ∀ n ∈ Nat.divisors 2880, Odd n → 5 ∣ n → ¬ 9 ∣ n → n = 5 ∨ n = 15 := by
    decide +kernel
  exact hcheck _ (Nat.mem_divisors.mpr ⟨hdiv, by decide⟩) ho h5 h9

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24Cartan
