module

public import GorensteinWalter.PSL2Cardinality
public import GorensteinWalter.PSL2TwoPartArithmetic
public import Mathlib.GroupTheory.Sylow

/-!
# The field two-part determined by an actual SL₂ Sylow subgroup

For a finite field of odd order, a Sylow `2`-subgroup of `SL₂` of order
`2^(n+1)`, with `n ≥ 2`, determines the exact two-part of `q-1` or
`q+1`, according to the field order modulo four. This is the numerical
step in Alperin–Brauer–Gorenstein, Chapter II, Proposition 3 (article
pages 25–26), relating the quaternion Sylow order to the matrix model.

The Sylow cardinality and the order formula for `SL₂` determine its
two-adic valuation. Dividing the order by two reduces to the existing
`PSL₂` two-part arithmetic. The resulting valuations give divisibility
and an odd complementary quotient. No field of odd order is excluded;
in particular the two branches retain orders three and nine.
-/

namespace GorensteinWalter

private lemma exact_two_part {m n : ℕ} (hm : m ≠ 0)
    (h : m.factorization 2 = n) : 2 ^ n ∣ m ∧ Odd (m / 2 ^ n) := by
  subst n
  exact ⟨Nat.ordProj_dvd m 2, (Nat.coprime_ordCompl Nat.prime_two hm).odd_of_left⟩

public theorem sl2_sylow_two_part_of_card
    (F : Type*) [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F))
    (n : ℕ) (hn : 2 ≤ n) (hP : Nat.card P = 2 ^ (n + 1)) :
    (Nat.card F % 4 = 1 ∧ 2 ^ n ∣ Nat.card F - 1 ∧
      Odd ((Nat.card F - 1) / 2 ^ n)) ∨
    (Nat.card F % 4 = 3 ∧ 2 ^ n ∣ Nat.card F + 1 ∧
      Odd ((Nat.card F + 1) / 2 ^ n)) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h2minus : 2 ∣ q - 1 := by
    rcases hodd with ⟨k, hk⟩
    exact ⟨k, by dsimp [q]; omega⟩
  have h2plus : 2 ∣ q + 1 := by
    rcases hodd with ⟨k, hk⟩
    exact ⟨k + 1, by dsimp [q]; omega⟩
  have hfac : (q * (q ^ 2 - 1)).factorization 2 = n + 1 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2 ^ (q * (q ^ 2 - 1)).factorization 2 = 2 ^ (n + 1)
    rw [← sl2_card_formula F, ← Sylow.card_eq_multiplicity P]
    exact hP
  have hdiv : 2 ∣ q * (q ^ 2 - 1) := by
    have hsquare : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      simpa using Nat.sq_sub_sq q 1
    rw [hsquare]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h2minus _) _
  have hhalf : (q * (q ^ 2 - 1) / 2).factorization 2 = n := by
    rw [Nat.factorization_div hdiv]
    change (q * (q ^ 2 - 1)).factorization 2 - (2 : ℕ).factorization 2 = n
    rw [hfac, Nat.Prime.factorization_self Nat.prime_two]
    omega
  have hminus : 2 * ((q - 1) / 2) = q - 1 := Nat.mul_div_cancel' h2minus
  rcases Nat.even_or_odd ((q - 1) / 2) with heven | hoddhalf
  · have hsplit := psl2_order_two_factorization_split hodd hq heven
    have hm : (q - 1).factorization 2 = n := by
      rw [Nat.factorization_div h2minus] at hsplit
      change (q * (q ^ 2 - 1) / 2).factorization 2 =
        (q - 1).factorization 2 - (2 : ℕ).factorization 2 + 1 at hsplit
      rw [hhalf, Nat.Prime.factorization_self Nat.prime_two] at hsplit
      omega
    refine Or.inl ⟨?_, exact_two_part (by omega) hm⟩
    rcases heven with ⟨k, hk⟩
    change q % 4 = 1
    omega
  · have hsplit := psl2_order_two_factorization_nonsplit hodd hq hoddhalf
    have hm : (q + 1).factorization 2 = n := by
      rw [Nat.factorization_div h2plus] at hsplit
      change (q * (q ^ 2 - 1) / 2).factorization 2 =
        (q + 1).factorization 2 - (2 : ℕ).factorization 2 + 1 at hsplit
      rw [hhalf, Nat.Prime.factorization_self Nat.prime_two] at hsplit
      omega
    refine Or.inr ⟨?_, exact_two_part (by omega) hm⟩
    rcases hoddhalf with ⟨k, hk⟩
    change q % 4 = 3
    omega

end GorensteinWalter

