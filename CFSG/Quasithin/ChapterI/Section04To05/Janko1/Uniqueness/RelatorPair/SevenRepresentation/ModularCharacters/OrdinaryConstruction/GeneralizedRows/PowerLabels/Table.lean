module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.PowerLabels.Normalization

/-!
# All powers from the aligned class seeds

Conjugacy respects taking powers. Consequently the squares of order-ten
powers and the cubes of order-fifteen powers are determined by the already
proved fifth-order cycles. Their element orders and these images distinguish
the required classes. Classes whose order occurs only once are immediate
from the order-of-a-power formula.

For order nineteen, the aligned square cycle gives eighth-power conjugacy.
Every nonzero residue modulo nineteen has the form `2^r * 8^k`, with `r < 3`
and `k < 6`; the small residue certificate checks the literal period orbits.
The final theorem handles every natural exponent by reduction modulo the
actual order of the representative. All finite certificates are kernel checked.

Source: the power conventions in `PowerData`, following Janko, J. Algebra 3
(1966), 147–186, and the ordinary calculation cited by Gorenstein, printed p.482.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
namespace PowerLabelConstruction
variable {G : Type*} [Group G] [Finite G] (c : OrdinaryClassData G)

private theorem single_order_detection : ∀ (j k : Fin 15) (n : Fin 20),
    (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 5 ∨ j = 6 ∨ j = 9) →
    classOrder k = classOrder j / Nat.gcd (classOrder j) n →
    k = ordinaryPowerClass j n := by decide +kernel

private theorem ten_detection : ∀ (j k : Fin 15) (n : Fin 20),
    (j = 7 ∨ j = 8) →
    classOrder k = classOrder j / Nat.gcd (classOrder j) n →
    (k = 3 → (4 : Fin 15) = ordinaryPowerClass (ordinaryPowerClass j 2) n) →
    (k = 4 → (3 : Fin 15) = ordinaryPowerClass (ordinaryPowerClass j 2) n) →
    (k = 7 → (4 : Fin 15) = ordinaryPowerClass (ordinaryPowerClass j 2) n) →
    (k = 8 → (3 : Fin 15) = ordinaryPowerClass (ordinaryPowerClass j 2) n) →
    k = ordinaryPowerClass j n := by decide +kernel

private theorem fifteen_detection : ∀ (j k : Fin 15) (n : Fin 20),
    (j = 10 ∨ j = 11) →
    classOrder k = classOrder j / Nat.gcd (classOrder j) n →
    (k = 3 → (4 : Fin 15) = ordinaryPowerClass (ordinaryPowerClass j 3) n) →
    (k = 4 → (3 : Fin 15) = ordinaryPowerClass (ordinaryPowerClass j 3) n) →
    (k = 10 → (4 : Fin 15) = ordinaryPowerClass (ordinaryPowerClass j 3) n) →
    (k = 11 → (3 : Fin 15) = ordinaryPowerClass (ordinaryPowerClass j 3) n) →
    k = ordinaryPowerClass j n := by decide +kernel

private theorem aligned_ten (h : Aligned c) (j : Fin 15) (hj : j = 7 ∨ j = 8)
    (n : Fin 20) : power c j n = ordinaryPowerClass j n := by
  have hseed : power c j 2 = ordinaryPowerClass j 2 := by
    rcases hj with rfl | rfl
    · exact h.ten.1
    · exact h.ten.2
  have ho : classOrder (power c j 2) = 5 := by
    rcases hj with rfl | rfl <;> exact power_order c _ 2
  have he : power c (power c j n) 2 =
      ordinaryPowerClass (ordinaryPowerClass j 2) n := by
    rw [power_mul, Nat.mul_comm (n : ℕ) 2, ← power_mul,
      power_five c h.five _ ho n, hseed]
  apply ten_detection j (power c j n) n hj (power_order c j n)
  all_goals intro hk; simpa only [hk, h.five.1, h.five.2, h.ten.1, h.ten.2] using he

private theorem aligned_fifteen (h : Aligned c) (j : Fin 15) (hj : j = 10 ∨ j = 11)
    (n : Fin 20) : power c j n = ordinaryPowerClass j n := by
  have hseed : power c j 3 = ordinaryPowerClass j 3 := by
    rcases hj with rfl | rfl
    · exact h.fifteen.1
    · exact h.fifteen.2
  have ho : classOrder (power c j 3) = 5 := by
    rcases hj with rfl | rfl <;> exact power_order c _ 3
  have he : power c (power c j n) 3 =
      ordinaryPowerClass (ordinaryPowerClass j 3) n := by
    rw [power_mul, Nat.mul_comm (n : ℕ) 3, ← power_mul,
      power_five c h.five _ ho n, hseed]
  have h33 : power c 3 3 = 4 := power_five c h.five 3 rfl 3
  have h43 : power c 4 3 = 3 := power_five c h.five 4 rfl 3
  apply fifteen_detection j (power c j n) n hj (power_order c j n)
  all_goals intro hk; simpa only [hk, h33, h43, h.fifteen.1, h.fifteen.2] using he

private theorem nineteen_residues : ∀ n : Fin 19, n ≠ 0 →
    ∃ (r : Fin 3) (k : Fin 6),
      (n : ℕ) = (2 ^ (r : ℕ) * 8 ^ (k : ℕ)) % 19 ∧
      ∀ j : Fin 15, classOrder j = 19 →
        ordinaryPowerClass j n = ordinaryPowerClass j (2 ^ (r : ℕ)) := by
  decide +kernel

private theorem aligned_nineteen_small (h : Aligned c) (j : Fin 15)
    (hj : classOrder j = 19) (r : Fin 3) :
    power c j (2 ^ (r : ℕ)) = ordinaryPowerClass j (2 ^ (r : ℕ)) := by
  have h4 (i : Fin 15) : power c i 4 = power c (power c i 2) 2 :=
    (power_mul c i 2 2).symm
  rcases (order_nineteen_iff j).mp hj with rfl | rfl | rfl <;>
    fin_cases r <;>
    simp [ordinaryPowerClass, ordinaryPowerCycle, classOrder, h4,
      h.nineteen.1, h.nineteen.2.1, h.nineteen.2.2]

private theorem aligned_nineteen_eight (h : Aligned c) (j : Fin 15)
    (hj : classOrder j = 19) : power c j 8 = j := by
  have he : power c j 8 = power c (power c (power c j 2) 2) 2 := by
    rw [power_mul, power_mul]
  rw [he]
  rcases (order_nineteen_iff j).mp hj with rfl | rfl | rfl <;>
    simp [h.nineteen.1, h.nineteen.2.1, h.nineteen.2.2]

private theorem aligned_nineteen (h : Aligned c) (j : Fin 15)
    (hj : classOrder j = 19) (n : ℕ) : power c j n = ordinaryPowerClass j n := by
  have h8 : ∀ k : ℕ, power c j (8 ^ k) = j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← power_mul, ih, aligned_nineteen_eight c h j hj]
  have hm : n % 19 < 19 := Nat.mod_lt _ (by decide)
  let t : Fin 19 := ⟨n % 19, hm⟩
  have ht : power c j n = power c j t := by
    exact (hj ▸ power_mod c j n).symm
  have ht' : ordinaryPowerClass j n = ordinaryPowerClass j t := by
    simp [ordinaryPowerClass, t, hj]
  rw [ht, ht']
  by_cases ht0 : t = 0
  · simp [ht0, ordinaryPowerClass_zero]
  obtain ⟨r, k, hnum, hclass⟩ := nineteen_residues t ht0
  rw [hclass j hj, hnum, ← hj, power_mod]
  rw [Nat.mul_comm (2 ^ (r : ℕ)), ← power_mul, h8]
  exact aligned_nineteen_small c h j hj r

public theorem aligned_power (h : Aligned c) (j : Fin 15) (n : ℕ) :
    power c j n = ordinaryPowerClass j n := by
  have hbound : ∀ i : Fin 15, 0 < classOrder i ∧ classOrder i < 20 := by decide +kernel
  let t : Fin 20 := ⟨n % classOrder j,
    (Nat.mod_lt _ (hbound j).1).trans (hbound j).2⟩
  have ht : power c j n = power c j t := (power_mod c j n).symm
  have ht' : ordinaryPowerClass j n = ordinaryPowerClass j t := by
    simp [ordinaryPowerClass, t]
  rw [ht, ht']
  fin_cases j
  all_goals first
    | exact single_order_detection _ _ t (by decide) (power_order c _ t)
    | exact power_five c h.five _ rfl t
    | exact aligned_ten c h _ (by decide) t
    | exact aligned_fifteen c h _ (by decide) t
    | exact aligned_nineteen c h _ rfl t

end PowerLabelConstruction
end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
