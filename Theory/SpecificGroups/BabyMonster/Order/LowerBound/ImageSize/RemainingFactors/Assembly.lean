module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Reduction
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Certificates for the factors of the Baby Monster order coprime to 30

The seven larger primes can be certified by element orders or, more cheaply,
by prime-length orbits of individual row vectors. A vector of period `p`
forces `p` to divide the order of the acting unit, hence the subgroup order.
This does not assert that the unit itself has order `p`.

The factor `7^2` requires a separate certificate. The final arithmetic lemma
combines that divisor with the seven larger primes using coprimality.
Concrete certificates are still required for each premise.

Candidate words and their provenance are recorded in `source/README.md`.
Source: ATLAS of Finite Group Representations, Baby Monster class representatives,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/B/ .
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound
namespace RemainingFactors

/-- The first fixed generator lies in the standard matrix subgroup. -/
theorem standardA_mem (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    standardA ha ∈ standardImage ha hb :=
  Subgroup.subset_closure (Set.mem_insert _ _)

/-- The second fixed generator lies in the standard matrix subgroup. -/
theorem standardB_mem (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    standardB hb ∈ standardImage ha hb :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- Positive words, with `false` denoting `a` and `true` denoting `b`. -/
def positiveWord (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) : List Bool → MatrixGroup
  | [] => 1
  | c :: w => (if c then standardB hb else standardA ha) * positiveWord ha hb w

/-- Every positive word in the fixed generators lies in the standard subgroup. -/
theorem positiveWord_mem (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) (w : List Bool) :
    positiveWord ha hb w ∈ standardImage ha hb := by
  induction w with
  | nil => exact (standardImage ha hb).one_mem
  | cons c w ih =>
    apply (standardImage ha hb).mul_mem _ ih
    cases c
    · exact standardA_mem ha hb
    · exact standardB_mem ha hb

private theorem iterate_vecMul (M : AtlasMatrix) (n : ℕ) (v : Fin 4370 → ZMod 2) :
    (fun v => Matrix.vecMul v M)^[n] v = Matrix.vecMul v (M ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, Matrix.vecMul_vecMul, pow_succ]

/-- A checked prime-length row-vector orbit certifies a prime divisor. -/
theorem prime_dvd_of_vector_period (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (g : MatrixGroup) (hg : g ∈ standardImage ha hb) {p : ℕ} (hp : p.Prime)
    (v : Fin 4370 → ZMod 2)
    (hperiod : Matrix.vecMul v ((g : AtlasMatrix) ^ p) = v)
    (hmove : Matrix.vecMul v (g : AtlasMatrix) ≠ v) :
    p ∣ Nat.card (standardImage ha hb) := by
  let f : (Fin 4370 → ZMod 2) → (Fin 4370 → ZMod 2) :=
    fun v => Matrix.vecMul v (g : AtlasMatrix)
  have : Fact p.Prime := ⟨hp⟩
  have hper : Function.IsPeriodicPt f p v := by
    change f^[p] v = v
    exact (iterate_vecMul _ _ _).trans hperiod
  have hmin : Function.minimalPeriod f v = p :=
    Function.minimalPeriod_eq_prime hper hmove
  have hfull : Function.IsPeriodicPt f (orderOf g) v := by
    change f^[orderOf g] v = v
    rw [show f = (fun v => Matrix.vecMul v (g : AtlasMatrix)) from rfl,
      iterate_vecMul, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one]
    exact Matrix.vecMul_one v
  exact (hmin ▸ hfull.minimalPeriod_dvd).trans
    ((standardImage ha hb).orderOf_dvd_natCard hg)

end RemainingFactors

/-- Assemble the remaining prime-power factors, keeping the square of seven
as a separate obligation. -/
theorem standardImage_remainingFactor_dvd_of_prime_divisors
    (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (h7 : 7 ^ 2 ∣ Nat.card (standardImage ha hb))
    (h11 : 11 ∣ Nat.card (standardImage ha hb))
    (h13 : 13 ∣ Nat.card (standardImage ha hb))
    (h17 : 17 ∣ Nat.card (standardImage ha hb))
    (h19 : 19 ∣ Nat.card (standardImage ha hb))
    (h23 : 23 ∣ Nat.card (standardImage ha hb))
    (h31 : 31 ∣ Nat.card (standardImage ha hb))
    (h47 : 47 ∣ Nat.card (standardImage ha hb)) :
    remainingOrderFactor ∣ Nat.card (standardImage ha hb) := by
  have h711 := (show Nat.Coprime (7 ^ 2) 11 by decide).mul_dvd_of_dvd_of_dvd h7 h11
  have h713 := (show Nat.Coprime (7 ^ 2 * 11) 13 by decide).mul_dvd_of_dvd_of_dvd h711 h13
  have h717 := (show Nat.Coprime (7 ^ 2 * 11 * 13) 17 by decide).mul_dvd_of_dvd_of_dvd h713 h17
  have h719 := (show Nat.Coprime (7 ^ 2 * 11 * 13 * 17) 19 by decide).mul_dvd_of_dvd_of_dvd h717 h19
  have h723 := (show Nat.Coprime (7 ^ 2 * 11 * 13 * 17 * 19) 23 by decide).mul_dvd_of_dvd_of_dvd h719 h23
  have h731 := (show Nat.Coprime (7 ^ 2 * 11 * 13 * 17 * 19 * 23) 31 by decide).mul_dvd_of_dvd_of_dvd h723 h31
  exact (show Nat.Coprime (7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31) 47 by decide).mul_dvd_of_dvd_of_dvd h731 h47

end BabyMonster.OrderLowerBound
