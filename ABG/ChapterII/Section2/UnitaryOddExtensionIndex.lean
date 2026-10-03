module
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Algebra.Ring.GeomSum
public import ABG.ChapterII.Section2.UnitaryCard
public import Mathlib.Tactic.Ring

/-!
# Odd index for a unitary group under an odd extension

For odd prime p and n=k*d with k nonzero and d odd, every injective
homomorphism from the original GU₂(p^k) into GU₂(p^n) has odd-index range.
The actual coefficient embedding is the intended consumer: this order
calculation supplies the fixed-unitary Sylow construction in ABG II.3,
Proposition 3(iv), article pp. 27–28. No model or action is replaced.

The proved order formula is q(q²−1)(q+1). Write a=p^k. The ratio of the
q²−1 factors is an odd-length geometric sum, and the ratio of the q factors
is the odd power a^(d−1). For d=2t+1, the remaining ratio is
1+a(a−1)Σ(i<t)(a²)^i, which is odd.
Injectivity identifies the range cardinality, and the index formula finishes.
-/

open scoped BigOperators

private theorem odd_geom_sum {k r : ℕ} (hk : Odd k) (hr : Odd r) :
    Odd (∑ i ∈ Finset.range r, k ^ i) := by
  rw [Finset.odd_sum_iff_odd_card_odd]
  simpa only [Finset.filter_true_of_mem (fun _ _ => hk.pow), Finset.card_range] using hr

private theorem odd_add_one_ratio {a d : ℕ} (ha : Odd a) (hd : Odd d) :
    ∃ b : ℕ, Odd b ∧ a ^ d + 1 = (a + 1) * b := by
  obtain ⟨t, rfl⟩ := hd
  have ha1 : 1 ≤ a := by have := Nat.odd_iff.mp ha; omega
  let S := ∑ i ∈ Finset.range t, (a ^ 2) ^ i
  have hgeom : S * (a ^ 2 - 1) + 1 = a ^ (2 * t) := by
    have h := geom_sum_mul_of_one_le (one_le_pow₀ (n := 2) ha1) t
    dsimp [S]
    rw [h, Nat.sub_add_cancel (one_le_pow₀ (one_le_pow₀ ha1)), ← pow_mul]
  have hsq : a ^ 2 - 1 = (a - 1) * (a + 1) := by
    simpa only [one_pow, mul_comm] using Nat.sq_sub_sq a 1
  refine ⟨1 + a * (a - 1) * S, ?_, ?_⟩
  · have he : Even (a - 1) := by
      rw [Nat.even_iff]
      have := Nat.odd_iff.mp ha
      omega
    exact odd_one.add_even ((he.mul_left a).mul_right S)
  · rw [pow_succ, ← hgeom, hsq]
    ring

private theorem unitary_card_ratio {a d : ℕ} (ha : Odd a) (hd : Odd d) :
    ∃ b : ℕ, Odd b ∧
      a ^ d * ((a ^ d) ^ 2 - 1) * (a ^ d + 1) =
        (a * (a ^ 2 - 1) * (a + 1)) * b := by
  have ha1 : 1 ≤ a := by have := Nat.odd_iff.mp ha; omega
  have hd1 : 1 ≤ d := by have := Nat.odd_iff.mp hd; omega
  obtain ⟨c, hc, hplus⟩ := odd_add_one_ratio ha hd
  let S := ∑ i ∈ Finset.range d, (a ^ 2) ^ i
  have hgeom : (a ^ d) ^ 2 - 1 = S * (a ^ 2 - 1) := by
    rw [geom_sum_mul_of_one_le (one_le_pow₀ (n := 2) ha1), ← pow_mul, ← pow_mul,
      Nat.mul_comm d 2]
  have he : a ^ d = a * a ^ (d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hd1]
  refine ⟨a ^ (d - 1) * S * c, (ha.pow.mul (odd_geom_sum ha.pow hd)).mul hc, ?_⟩
  rw [hgeom, hplus, he]
  ring

namespace ABG

public theorem GU2_odd_index_of_injective
    (p k n : ℕ) [Fact p.Prime] (hp : Odd p) (hk : k ≠ 0) (hn : n ≠ 0)
    (d : ℕ) (hd : Odd d) (hnk : n = k * d)
    (f : GU2 p k hk →* GU2 p n hn) (hf : Function.Injective f) :
    Odd f.range.index := by
  have hc : Nat.card f.range = Nat.card (GU2 p k hk) :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  obtain ⟨b, hb, he⟩ := unitary_card_ratio (show Odd (p ^ k) from hp.pow) hd
  have hratio : Nat.card (GU2 p n hn) = Nat.card (GU2 p k hk) * b := by
    rw [GU2_card p n hp hn, GU2_card p k hp hk, hnk, pow_mul]
    exact he
  have hi : f.range.index = b := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := GU2 p k hk))
    rw [← hc, Subgroup.card_mul_index, hc]
    exact hratio
  rwa [hi]

end ABG
