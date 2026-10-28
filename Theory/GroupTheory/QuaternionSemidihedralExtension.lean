module

public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Semidihedral generators from a moving quaternion element

If an involution moves a quaternion element modulo the central involution,
their product has order eight and satisfies the semidihedral relation.
Its square lies in the quaternion subgroup and conjugates the involution
to its product with the central involution. A group of order at most sixteen
containing these generators is the concrete standard semidihedral group.

Only a table on two elements of Q₈ is needed; the ambient group calculations
and cardinality argument are structural. The application is the final step
of Aschbacher–Smith J.2.5–6, printed pp.434–435 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
namespace Semidihedral
private theorem quaternion_pair (p q : QuaternionGroup 2)
    (ho : (p = 1 ↔ q = 1) ∧ (p ^ 2 = 1 ↔ q ^ 2 = 1)) (hne : p * q⁻¹ ≠ 1)
    (hnz : p * q⁻¹ ≠ QuaternionGroup.a 2) :
    (q * p) ^ 2 = QuaternionGroup.a 2 ∧ q * p * q = p := by
  revert p q
  decide +kernel

variable {G : Type*} [Group G]
/-- A moving quaternion element constructs the rotation and an explicit fusion conjugator. -/
theorem quaternion_twisted_generators (f : QuaternionGroup 2 →* G)
    (hf : Function.Injective f) (i : G) (hi : i ^ 2 = 1)
    (p q : QuaternionGroup 2) (ho : orderOf p = orderOf q)
    (hne : p * q⁻¹ ≠ 1) (hnz : p * q⁻¹ ≠ QuaternionGroup.a 2)
    (hc : i * f q * i⁻¹ = f p) :
    orderOf (f q * i) = 8 ∧
    i * (f q * i) * i⁻¹ = (f q * i) ^ 3 ∧
    (f q * i) ^ 4 = f (QuaternionGroup.a 2) ∧
    (f q * i) ^ 2 = f (q * p) ∧
    f (q * p) * i * (f (q * p))⁻¹ = i * f (QuaternionGroup.a 2) := by
  have horders : (p = 1 ↔ q = 1) ∧ (p ^ 2 = 1 ↔ q ^ 2 = 1) := by
    constructor
    · simpa only [orderOf_eq_one_iff] using (show orderOf p = 1 ↔ orderOf q = 1 by rw [ho])
    · rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one, ho]
  obtain ⟨hs, hp⟩ := quaternion_pair p q horders hne hnz
  have hswap : i * f q = f p * i := mul_inv_eq_iff_eq_mul.mp hc
  have htwo : (f q * i) ^ 2 = f (q * p) := by
    rw [pow_two, mul_assoc (f q) i, ← mul_assoc i, hswap]
    simp only [mul_assoc, ← pow_two, hi, mul_one, map_mul]
  have hfour : (f q * i) ^ 4 = f (QuaternionGroup.a 2) := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, htwo, ← map_pow, hs]
  have hrel : i * (f q * i) * i⁻¹ = (f q * i) ^ 3 := by
    calc
      _ = f p * i := by rw [← mul_assoc, hswap]; group
      _ = f (q * p * q) * i := by rw [hp]
      _ = (f q * i) ^ 2 * (f q * i) := by rw [htwo]; simp only [map_mul, mul_assoc]
      _ = _ := (pow_succ (f q * i) 2).symm
  have horder : orderOf (f q * i) = 8 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 2)
    · change (f q * i) ^ 4 ≠ 1
      rw [hfour]
      intro he
      exact (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1)
        (hf (he.trans f.map_one.symm))
    · change (f q * i) ^ 8 = 1
      rw [show 8 = 4 * 2 from rfl, pow_mul, hfour, ← map_pow]
      exact f.map_one
  refine ⟨horder, hrel, hfour, htwo, ?_⟩
  rw [← htwo, ← hfour]
  let a := f q * i
  have hmove : i * a ^ 2 = a ^ 6 * i := by
    have he := congrArg (fun g : G => g ^ 2) hrel
    rw [conj_pow, ← pow_mul] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have ha8 : a ^ 8 = 1 := horder ▸ pow_orderOf_eq_one a
  apply mul_right_cancel (b := a ^ 2)
  calc
    (a ^ 2 * i * (a ^ 2)⁻¹) * a ^ 2 = a ^ 2 * i := by group
    _ = a ^ 8 * (a ^ 2 * i) := by rw [ha8, one_mul]
    _ = a ^ 4 * (a ^ 6 * i) := by rw [← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add]
    _ = a ^ 4 * (i * a ^ 2) := by rw [hmove]
    _ = (i * a ^ 4) * a ^ 2 := by
      have hc4 : i * a ^ 4 * i⁻¹ = a ^ 4 := by
        have he := congrArg (fun g : G => g ^ 4) hrel
        rw [conj_pow, ← pow_mul] at he
        rw [show 3 * 4 = 8 + 4 from rfl, pow_add, ha8, one_mul] at he
        exact he
      rw [← mul_assoc, ← mul_inv_eq_iff_eq_mul.mp hc4]

/-- An order-eight rotation with semidihedral twist saturates an upper bound of sixteen. -/
theorem equiv_of_small_twisted_generators [Finite G] (a b : G)
    (ha : orderOf a = 8) (hb : b ^ 2 = 1)
    (hab : b * a * b⁻¹ = a ^ 3) (hcard : Nat.card G ≤ 16) :
    Nonempty (G ≃* StandardModel 4 (by decide)) := by
  have hbN : b ∉ zpowers a := by
    rintro ⟨k, rfl⟩
    have hc : a ^ k * a * (a ^ k)⁻¹ = a := by
      rw [(Commute.zpow_left (Commute.refl a) k).eq, mul_inv_cancel_right]
    rw [hc] at hab
    have hsq : a ^ 2 = 1 := by
      apply mul_left_cancel (a := a)
      calc
        a * a ^ 2 = a ^ 3 := by group
        _ = a := hab.symm
        _ = a * 1 := (mul_one a).symm
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [ha] at hd
    norm_num at hd
  have hNtop : zpowers a ≠ ⊤ := fun he => hbN (he ▸ mem_top b)
  have hind := one_lt_index_of_ne_top hNtop
  have hcount := (zpowers a).card_mul_index
  rw [Nat.card_zpowers, ha] at hcount
  have hG : Nat.card G = 16 := by omega
  let C := closure ({a, b} : Set G)
  have haC : a ∈ C := subset_closure (by simp)
  have hbC : b ∈ C := subset_closure (by simp)
  have hNC : zpowers a ≤ C := zpowers_le.mpr haC
  have hCgt : 8 < Nat.card C := by
    have hn := card_le_of_le hNC
    rw [Nat.card_zpowers, ha] at hn
    have hne : Nat.card C ≠ 8 := by
      intro he
      have heq : zpowers a = C := eq_of_le_of_card_ge hNC (by rw [he, Nat.card_zpowers, ha])
      exact hbN (heq.symm ▸ hbC)
    omega
  have hCtop : C = ⊤ := by
    by_contra hne
    have hcindex : 2 ≤ C.index := one_lt_index_of_ne_top hne
    have hm := Nat.mul_le_mul (show 9 ≤ Nat.card C by omega) hcindex
    rw [C.card_mul_index, hG] at hm
    omega
  exact standardModel_equiv_of_relations (by decide : 4 ≤ 4) a b
    (show a ^ 8 = 1 from ha ▸ pow_orderOf_eq_one a) hb hab hCtop hG

end Semidihedral
