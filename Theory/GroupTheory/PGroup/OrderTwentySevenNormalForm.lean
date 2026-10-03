module

public import Theory.GroupTheory.PGroup.OrderTwentySeven
import Mathlib.Tactic.Group

/-!
# Normal forms for groups of exponent three and class two

If `y * x = c * x * y` with `c` central, multiplication of the words
`x^i * y^j * c^k` is given by the usual Heisenberg coordinate law. When the
three generators cube to one, all coordinates can be taken modulo three.
In a group of order 27, any subgroup containing noncommuting elements is the
whole group, since groups of order 1, 3, and 9 are abelian.

These are the abstract ingredients in recognizing the Hermitian root group.
Source: Suzuki (1965), Section IV, printed pp. 7–10.
-/

namespace OrderTwentySeven
open scoped commutatorElement

variable {G : Type*} [Group G]

private lemma swap_powers (x y c : G) (hc : c ∈ Subgroup.center G)
    (hs : y * x = c * x * y) (j i : ℕ) :
    y ^ j * x ^ i = c ^ (j * i) * x ^ i * y ^ j := by
  have hcx (n m : ℕ) : Commute (c ^ n) (x ^ m) :=
    (show Commute c x from (Subgroup.mem_center_iff.mp hc x).symm).pow_pow n m
  have hcy (n m : ℕ) : Commute (c ^ n) (y ^ m) :=
    (show Commute c y from (Subgroup.mem_center_iff.mp hc y).symm).pow_pow n m
  have hs1 (j : ℕ) : y ^ j * x = c ^ j * x * y ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        y ^ (j+1) * x = y ^ j * (y * x) := by group
        _ = y ^ j * (c * x * y) := by rw [hs]
        _ = c * (y ^ j * x) * y := by
          have hh := (hcy 1 j).symm.left_comm (x * y)
          simpa only [pow_one, mul_assoc] using hh
        _ = c * (c ^ j * x * y ^ j) * y := by rw [ih]
        _ = c ^ (j+1) * x * y ^ (j+1) := by rw [pow_succ, pow_succ']; group
  induction i with
  | zero => simp
  | succ i ih =>
    calc
      y ^ j * x ^ (i+1) = (y ^ j * x ^ i) * x := by rw [pow_succ, mul_assoc]
      _ = (c ^ (j*i) * x ^ i * y ^ j) * x := by rw [ih]
      _ = c ^ (j*i) * x ^ i * (c ^ j * x * y ^ j) := by simp only [mul_assoc, hs1]
      _ = (c ^ (j*i) * c ^ j) * (x ^ i * x) * y ^ j := by
        simpa only [mul_assoc] using congrArg (fun z => c ^ (j*i) * z)
          ((hcx j i).symm.left_comm (x * y ^ j))
      _ = c ^ (j*(i+1)) * x ^ (i+1) * y ^ j := by rw [← pow_add, ← pow_succ, Nat.mul_add, Nat.mul_one]

private lemma normal_mul (x y c : G) (hc : c ∈ Subgroup.center G)
    (hs : y * x = c * x * y) (i j k l m n : ℕ) :
    (x ^ i * y ^ j * c ^ k) * (x ^ l * y ^ m * c ^ n) =
      x ^ (i+l) * y ^ (j+m) * c ^ (k+n+j*l) := by
  have hcz (a : ℕ) (z : G) : Commute (c ^ a) z :=
    (show Commute c z from (Subgroup.mem_center_iff.mp hc z).symm).pow_left a
  calc
    _ = x ^ i * (y ^ j * x ^ l) * y ^ m * (c ^ k * c ^ n) := by
      rw [mul_assoc (x ^ i * y ^ j)]
      rw [show c ^ k * (x ^ l * y ^ m * c ^ n) =
        (x ^ l * y ^ m) * (c ^ k * c ^ n) by
          rw [← mul_assoc, (hcz k (x ^ l * y ^ m)).eq, mul_assoc]]
      simp only [mul_assoc]
    _ = x ^ i * (c ^ (j*l) * x ^ l * y ^ j) * y ^ m * (c ^ k * c ^ n) := by
      rw [swap_powers x y c hc hs]
    _ = (x ^ i * x ^ l) * (y ^ j * y ^ m) * ((c ^ k * c ^ n) * c ^ (j*l)) := by
      simp only [mul_assoc]
      rw [(hcz (j*l) (x ^ l * (y ^ j * (y ^ m * (c ^ k * c ^ n))))).eq]
      simp only [mul_assoc]
    _ = _ := by simp only [pow_add, mul_assoc]

public abbrev Coordinates := Fin 3 × Fin 3 × Fin 3

@[expose] public def coordinateProduct (s t : Coordinates) : Coordinates :=
  (s.1 + t.1, s.2.1 + t.2.1, s.2.2 + t.2.2 + s.2.1 * t.1)

@[expose] public def evaluate (x y c : G) (t : Coordinates) : G :=
  x ^ t.1.val * y ^ t.2.1.val * c ^ t.2.2.val

public theorem evaluate_coordinateProduct (x y c : G) (hc : c ∈ Subgroup.center G)
    (hs : y * x = c * x * y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : c ^ 3 = 1)
    (s t : Coordinates) :
    evaluate x y c (coordinateProduct s t) = evaluate x y c s * evaluate x y c t := by
  simp only [evaluate, coordinateProduct, Fin.val_add, Fin.val_mul]
  rw [normal_mul x y c hc hs]
  rw [pow_eq_pow_mod (s.1.val + t.1.val) hx,
    pow_eq_pow_mod (s.2.1.val + t.2.1.val) hy,
    pow_eq_pow_mod (s.2.2.val + t.2.2.val + s.2.1.val * t.1.val) hz]
  congr 2
  omega

public theorem subgroup_eq_top_of_noncommuting {P : Type*} [Group P] [Finite P]
    (hP : Nat.card P = 27) (H : Subgroup P) (x y : H) (hxy : x * y ≠ y * x) : H = ⊤ := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : Nat.card H ∣ 27 := hP ▸ H.card_subgroup_dvd_card
  have hm : Nat.card H ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hdiv : Nat.divisors 27 = {1,3,9,27} := by decide
  rw [hdiv] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h
  · let : IsCyclic H := isCyclic_of_card_dvd_prime (p := 3) (by rw [h]; exact one_dvd _)
    exact (hxy (IsMulCommutative.is_comm.comm x y)).elim
  · let : IsCyclic H := isCyclic_of_card_dvd_prime (p := 3) (by rw [h])
    exact (hxy (IsMulCommutative.is_comm.comm x y)).elim
  · let : IsMulCommutative H := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by simpa using h)
    exact (hxy (IsMulCommutative.is_comm.comm x y)).elim
  · exact (Subgroup.card_eq_iff_eq_top H).mp (h.trans hP.symm)

end OrderTwentySeven
