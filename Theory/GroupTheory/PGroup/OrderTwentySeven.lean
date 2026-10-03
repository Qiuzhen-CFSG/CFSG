module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.NormNum

/-!
# Nonabelian groups of order twenty-seven

The center has order three and its quotient is elementary abelian of order nine.
Consequently commutators are central of exponent three, and cubing is a
homomorphism into the center. If an element has order nine, the cube map has
image of order three and every nonempty fiber has order nine.

These elementary structural facts underlie the order-27 argument in
Wong (1964), pp. 108–109. The center calculation is extracted from the
corresponding private argument in `Theory.Alternating.theorem_5_2_3`.
-/

open scoped commutatorElement

namespace OrderTwentySeven

public theorem center_card
    {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 27) (hncomm : ¬ IsMulCommutative P) :
    Nat.card (Subgroup.center P) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardPow : Nat.card P = 3 ^ 3 := by
    simpa using hcard
  obtain ⟨k, hkpos, hcenter⟩ :=
    IsPGroup.card_center_eq_prime_pow hcardPow (by norm_num)
  have hk_dvd : 3 ^ k ∣ 3 ^ 3 := by
    rw [← hcenter, ← hcardPow]
    simpa [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le
        (show Subgroup.center P ≤ (⊤ : Subgroup P) from le_top))
  have hkle : k ≤ 3 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hk_dvd
  have hkCases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkCases with hk1 | hk23
  · simpa [hk1] using hcenter
  · rcases hk23 with hk2 | hk3
    · have hindex : (Subgroup.center P).index = 3 := by
        have hmul := (Subgroup.center P).card_mul_index
        rw [hcenter, hk2, hcard] at hmul
        omega
      have hquotCard : Nat.card (P ⧸ Subgroup.center P) = 3 := by
        rw [← Subgroup.index_eq_card]
        exact hindex
      let : IsCyclic (P ⧸ Subgroup.center P) :=
        isCyclic_of_card_dvd_prime (by rw [hquotCard])
      exact (hncomm
        (isMulCommutative_of_isCyclic_quotient_center_self P)).elim
    · have hcenterCard : Nat.card (Subgroup.center P) = Nat.card P := by
        rw [hcenter, hk3, hcardPow]
      have hcenterTop : Subgroup.center P = ⊤ :=
        (Subgroup.card_eq_iff_eq_top _).mp hcenterCard
      exact (hncomm (Subgroup.center_eq_top_iff.mp hcenterTop)).elim

variable {P : Type*} [Group P] [Finite P]

public theorem quotient_center_card (hcard : Nat.card P = 27)
    (hncomm : ¬ IsMulCommutative P) : Nat.card (P ⧸ Subgroup.center P) = 9 := by
  have hm := (Subgroup.center P).card_mul_index
  rw [center_card hcard hncomm, hcard] at hm
  rw [← Subgroup.index_eq_card]
  omega

public theorem cube_mem_center (hcard : Nat.card P = 27)
    (hncomm : ¬ IsMulCommutative P) (x : P) : x ^ 3 ∈ Subgroup.center P := by
  let Q := P ⧸ Subgroup.center P
  let q := QuotientGroup.mk' (Subgroup.center P)
  have hQ : Nat.card Q = 9 := quotient_center_card hcard hncomm
  have hd : orderOf (q x) ∣ 9 := hQ ▸ orderOf_dvd_natCard (q x)
  have hm : orderOf (q x) ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [hdiv] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hp : q x ^ 3 = 1 := by
    rcases hm with h | h | h
    · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h]; exact one_dvd _)
    · rw [← h]; exact pow_orderOf_eq_one _
    · let : IsCyclic Q := isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨q x, h.trans hQ.symm⟩
      exact (hncomm (isMulCommutative_of_isCyclic_quotient_center_self P)).elim
  exact (QuotientGroup.eq_one_iff _).mp (by change q (x ^ 3) = 1; simpa only [map_pow] using hp)

public theorem commutator_mem_center (hcard : Nat.card P = 27)
    (hncomm : ¬ IsMulCommutative P) (x y : P) : ⁅x, y⁆ ∈ Subgroup.center P := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsMulCommutative (P ⧸ Subgroup.center P) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (p := 3) (by simpa using quotient_center_card hcard hncomm)
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (Subgroup.center P)) ⁅x, y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (IsMulCommutative.is_comm.comm _ _)

/-- Cubing is multiplicative in a nonabelian group of order twenty-seven. -/
public theorem cube_mul (hcard : Nat.card P = 27)
    (hncomm : ¬ IsMulCommutative P) (x y : P) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  let c := ⁅y, x⁆
  have hc : c ∈ Subgroup.center P := commutator_mem_center hcard hncomm y x
  have hc3 : c ^ 3 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa only [center_card hcard hncomm] using (Subgroup.center P).orderOf_dvd_natCard hc
  have hswap : y * x = c * x * y := by simp [c, commutatorElement_def, mul_assoc]
  have hxc : x * c = c * x := Subgroup.mem_center_iff.mp hc x
  have hyc : y * c = c * y := Subgroup.mem_center_iff.mp hc y
  have hxca (z : P) : x * (c * z) = c * (x * z) := by rw [← mul_assoc, hxc, mul_assoc]
  have hyca (z : P) : y * (c * z) = c * (y * z) := by rw [← mul_assoc, hyc, mul_assoc]
  have hs (z : P) : y * (x * z) = c * (x * (y * z)) := by
    rw [← mul_assoc, hswap]; simp only [mul_assoc]
  calc
    (x * y) ^ 3 = c ^ 3 * (x ^ 3 * y ^ 3) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc, hs, hxca, hyca]
    _ = x ^ 3 * y ^ 3 := by rw [hc3, one_mul]

/-- The cube map of a nonabelian group of order twenty-seven. -/
public def cubeHom (hcard : Nat.card P = 27) (hncomm : ¬ IsMulCommutative P) : P →* P where
  toFun x := x ^ 3
  map_one' := one_pow 3
  map_mul' := cube_mul hcard hncomm

@[simp] public theorem cubeHom_apply (hcard : Nat.card P = 27)
    (hncomm : ¬ IsMulCommutative P) (x : P) : cubeHom hcard hncomm x = x ^ 3 := by rfl

/-- An order-nine element makes the cube map's image have order three. -/
public theorem cubeHom_range_card (hcard : Nat.card P = 27)
    (hncomm : ¬ IsMulCommutative P) (a : P) (ha : orderOf a = 9) :
    Nat.card (cubeHom hcard hncomm).range = 3 := by
  let f := cubeHom hcard hncomm
  have hle : f.range ≤ Subgroup.center P := by
    rintro x ⟨y, rfl⟩
    exact cube_mem_center hcard hncomm y
  have hd : Nat.card f.range ∣ 3 := by
    rw [← center_card hcard hncomm]
    exact Subgroup.card_dvd_of_le hle
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h | h
  · have hbot : f.range = ⊥ := (Subgroup.card_eq_one).mp h
    have ha3 : a ^ 3 = 1 := by
      have hm : f a ∈ f.range := ⟨a, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hm
    have hd := orderOf_dvd_of_pow_eq_one ha3
    rw [ha] at hd
    norm_num at hd
  · exact h

/-- Every fiber above the cube of an order-nine element has nine elements. -/
public theorem cube_fiber_card_of_order_nine (hcard : Nat.card P = 27)
    (hncomm : ¬ IsMulCommutative P) (a : P) (ha : orderOf a = 9) :
    Nat.card {x : P // x ^ 3 = a ^ 3} = 9 := by
  let f := cubeHom hcard hncomm
  have hr : Nat.card f.range = 3 := cubeHom_range_card hcard hncomm a ha
  have hk : Nat.card f.ker = 9 := by
    have hm := f.ker.card_mul_index
    rw [Subgroup.index_ker, hr, hcard] at hm
    omega
  calc
    Nat.card {x : P // x ^ 3 = a ^ 3} = Nat.card f.ker :=
      Nat.card_congr ((Equiv.subtypeEquivRight
        (fun x => show x ^ 3 = a ^ 3 ↔ x ∈ f ⁻¹' {f a} by simp [f])).trans
          (f.fiberEquivKer a))
    _ = 9 := hk

end OrderTwentySeven
