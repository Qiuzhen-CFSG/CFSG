module

public import Theory.Representation.ReeF4.BinaryDegree.PeriodicProduct
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Products with a triality-twisted period

Suppose a sequence of positive factor degrees comes from labels with a diagram
symmetry. Moving by `n` applies that symmetry, while moving by `s` fixes the
labels, where `s` divides `3*n`. Every nontrivial factor has degree at least
eight, and a nontrivial diagram-fixed factor has degree at least 24. Then `s`
times the product of the first `n` factor degrees is at least `24*n`.

The degrees repeat with period `gcd n s`. Two or more repeated blocks give
`8^t ≥ 24*t`. With one block, `s` is either `n` or `3*n`: the first case fixes
each label under the diagram symmetry; the second supplies the factor three
in the field degree. This includes `n = 1` and every proper-subfield period.

This is only the numerical implication used in binary triality descent. The
existence and degrees of representation factors are separate mathematical
inputs. Source: GLS3 §2.8, especially Corollary 2.8.6(a) and Remark 2.8.8;
Aschbacher--Smith, *The Classification of Quasithin Groups*, printed p.356.
-/

public section
namespace Triality.BinaryDegree
open Representation.FrobeniusTensor

private theorem periodic_gcd {α : Type*} {a : ℕ → α} {m n : ℕ}
    (hm : Function.Periodic a m) (hn : Function.Periodic a n) :
    Function.Periodic a (Nat.gcd m n) := by
  let shift : (ℕ → α) → (ℕ → α) := fun b i => b (i + 1)
  have hit (k : ℕ) (b : ℕ → α) (i : ℕ) : shift^[k] b i = b (i + k) := by
    induction k generalizing b i with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change shift^[k] b (i + 1) = b (i + (k + 1))
      rw [ih]
      congr 1
      omega
  have hp (k : ℕ) : Function.IsPeriodicPt shift k a ↔ Function.Periodic a k := by
    change shift^[k] a = a ↔ _
    simp only [funext_iff, hit, Function.Periodic]
  exact (hp _).mp (((hp m).mpr hm).gcd ((hp n).mpr hn))

private theorem twenty_four_mul_le_eight_pow {t : ℕ} (ht : 2 ≤ t) :
    24 * t ≤ 8 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

private theorem factor_le_product {a : ℕ → ℕ} {n i : ℕ}
    (hn : 0 < n) (ha : Function.Periodic a n) (hpos : ∀ j, 0 < a j) :
    a i ≤ ∏ j ∈ Finset.range n, a j := by
  have h := Finset.single_le_prod' (f := a) (s := Finset.range n)
    (fun j _ => hpos j) (Finset.mem_range.mpr (Nat.mod_lt i hn))
  rwa [ha.map_mod_nat] at h

/-- The numerical bound for all periods of a tensor sequence whose wraparound
is a diagram action of order three. -/
theorem twenty_four_mul_le_twisted_product {α : Type*} {w : ℕ → α}
    {d : α → ℕ} {τ : α → α} {n s : ℕ}
    (hn : 0 < n) (hs : 0 < s) (hsn : s ∣ 3 * n)
    (htwist : ∀ i, w (i + n) = τ (w i))
    (hd : ∀ x, d (τ x) = d x)
    (hperiod : Function.Periodic w s)
    (hpos : ∀ i, 0 < d (w i)) (hlarge : ∃ i, 8 ≤ d (w i))
    (hfixed : ∀ i, τ (w i) = w i → 8 ≤ d (w i) → 24 ≤ d (w i)) :
    24 * n ≤ s * ∏ i ∈ Finset.range n, d (w i) := by
  let a := fun i => d (w i)
  have han : Function.Periodic a n := fun i => by dsimp [a]; rw [htwist, hd]
  have has : Function.Periodic a s := hperiod.comp d
  have hag : Function.Periodic a (Nat.gcd n s) := periodic_gcd han has
  have hg : 0 < Nat.gcd n s := Nat.gcd_pos_of_pos_left s hn
  have hgs : Nat.gcd n s ≤ s := Nat.le_of_dvd hs (Nat.gcd_dvd_right n s)
  obtain ⟨t, hnt⟩ := Nat.gcd_dvd_left n s
  have ht : 0 < t := by
    by_contra! h
    have : t = 0 := by omega
    simp [this] at hnt
    omega
  by_cases ht1 : t = 1
  · have hng : n = Nat.gcd n s := by simpa [ht1] using hnt
    have hns : n ∣ s := hng ▸ Nat.gcd_dvd_right n s
    obtain ⟨k, hsk⟩ := hns
    have hk : k ∣ 3 := by
      rw [hsk, Nat.mul_comm 3 n] at hsn
      exact (Nat.mul_dvd_mul_iff_left hn).mp hsn
    have hk13 : k = 1 ∨ k = 3 := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hk
    rcases hk13 with rfl | rfl
    · have hsn' : s = n := by simpa using hsk
      obtain ⟨i, hi⟩ := hlarge
      have hfix : τ (w i) = w i := by rw [← htwist, ← hsn']; exact hperiod i
      have h24 : 24 ≤ ∏ j ∈ Finset.range n, a j :=
        (hfixed i hfix hi).trans (factor_le_product hn han hpos)
      rw [hsn']
      nlinarith
    · obtain ⟨i, hi⟩ := hlarge
      have h8 : 8 ≤ ∏ j ∈ Finset.range n, a j :=
        hi.trans (factor_le_product hn han hpos)
      rw [hsk]
      nlinarith
  · have ht2 : 2 ≤ t := by omega
    obtain ⟨i, hi⟩ := hlarge
    have h8 : 8 ≤ ∏ j ∈ Finset.range (Nat.gcd n s), a j :=
      hi.trans (factor_le_product hg hag hpos)
    have hb := (twenty_four_mul_le_eight_pow ht2).trans (Nat.pow_le_pow_left h8 t)
    change 24 * n ≤ s * ∏ i ∈ Finset.range n, a i
    rw [hnt, prod_range_mul_of_periodic hag]
    nlinarith

end Triality.BinaryDegree
