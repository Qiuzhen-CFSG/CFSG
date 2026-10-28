module
public import Theory.Combinatorics.PeriodicBinaryWeight
/-!
# Binary weights of degree four

A product of one plus the binary digits equals four precisely when two
bits are nonzero. Division by two isolates the lowest bit and reduces the
remaining product to four or two. This supplies the actual two Frobenius
positions for four-dimensional irreducible SL₂ modules.
-/

namespace Nat.BinaryDegreeFour
private def digitProd (m n : ℕ) : ℕ := ∏ i : Fin m, (n / 2 ^ (i : ℕ) % 2 + 1)
private theorem digitProd_succ (m n : ℕ) :
    digitProd (m+1) n = (n%2+1)*digitProd m (n/2) := by
  rw [digitProd, Fin.prod_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.div_one]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul, mul_comm]
private theorem eq_zero_of_prod_one (m n : ℕ) (hn : n < 2^m)
    (h : digitProd m n = 1) : n=0 := by
  induction m generalizing n with
  | zero => simpa using hn
  | succ m ih =>
    rw [digitProd_succ] at h
    have hp : 0 < digitProd m (n/2) := Finset.prod_pos (fun _ _ => Nat.zero_lt_succ _)
    have hle := Nat.le_mul_of_pos_left (digitProd m (n/2)) (Nat.zero_lt_succ (n%2))
    rw [h] at hle
    have hq : digitProd m (n/2)=1 := by omega
    have hr : n%2=0 := by rw [hq] at h; omega
    have hn' : n/2 < 2^m := Nat.div_lt_of_lt_mul (by simpa [pow_succ,mul_comm] using hn)
    have hz := ih (n/2) hn' hq
    omega
private theorem pow_of_prod_two (m n : ℕ) (hn : n < 2^m)
    (h : digitProd m n = 2) : ∃ j<m, n=2^j := by
  induction m generalizing n with
  | zero => simp [digitProd] at h
  | succ m ih =>
    rw [digitProd_succ] at h
    have hn' : n/2 < 2^m := Nat.div_lt_of_lt_mul (by simpa [pow_succ,mul_comm] using hn)
    by_cases hr : n%2=0
    · have hq : digitProd m (n/2)=2 := by simpa [hr] using h
      obtain ⟨j,hj,he⟩ := ih (n/2) hn' hq
      refine ⟨j+1,by omega,?_⟩
      rw [pow_succ]
      omega
    · have hr1 : n%2=1 := by omega
      have hq : digitProd m (n/2)=1 := by rw [hr1] at h; omega
      have hz := eq_zero_of_prod_one m (n/2) hn' hq
      exact ⟨0,by omega,by simp; omega⟩

public theorem exists_two_bits (m n : ℕ) (hn : n < 2^m)
    (h : (∏ i : Fin m, (n / 2 ^ (i : ℕ) % 2 + 1)) = 4) :
    ∃ j k : ℕ, j<k ∧ k<m ∧ n=2^j+2^k := by
  change digitProd m n = 4 at h
  induction m generalizing n with
  | zero => simp [digitProd] at h
  | succ m ih =>
    rw [digitProd_succ] at h
    have hn' : n/2 < 2^m := Nat.div_lt_of_lt_mul (by simpa [pow_succ,mul_comm] using hn)
    by_cases hr : n%2=0
    · have hq : digitProd m (n/2)=4 := by simpa [hr] using h
      obtain ⟨j,k,hjk,hkm,he⟩ := ih (n/2) hn' hq
      refine ⟨j+1,k+1,by omega,by omega,?_⟩
      rw [pow_succ,pow_succ]
      omega
    · have hr1 : n%2=1 := by omega
      have hq : digitProd m (n/2)=2 := by rw [hr1] at h; omega
      obtain ⟨k,hk,he⟩ := pow_of_prod_two m (n/2) hn' hq
      refine ⟨0,k+1,by omega,by omega,?_⟩
      rw [pow_zero,pow_succ]
      omega
end Nat.BinaryDegreeFour
