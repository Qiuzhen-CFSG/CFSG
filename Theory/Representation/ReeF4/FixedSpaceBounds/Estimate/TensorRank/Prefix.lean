module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.TensorRank.Linear
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.AlgebraicFactors

/-!
# Displacement along the actual recursive tensor product

For a nonzero family of characteristic-two representations, suppose each
factor of dimension at least `d` has involution displacement at least `b`.
If `c > 0` such factors occur in the first `n` positions, the actual
`tensorPrefix` has displacement at least `b*d^(c-1)`. The first large
factor supplies `b`; each later large factor multiplies the lower bound by
at least `d`. All other factors have positive dimension. This induction
uses the existing source order and requires no tensor reindexing.

For `d >= 2`, the exponential bound implies the linear bound `b*c`.

Source: Guralnick--Malle, *Classification of 2F-modules, II*,
Corollary 2.11(a), applied successively to the actual tensor factors.
-/

public section

open Module
open Representation.BinaryOffender.NaturalTensor
open Representation.TensorInvolutionDisplacement
open ReeF4.BinaryDegree.ExceptionalTensor

namespace ReeF4.FixedSpaceEstimate

variable {K G : Type*} [Field K] [Group G]

/-- Number of factors meeting the specified dimension threshold. -/
@[expose] noncomputable def largeFactorCount (V : ℕ → FDRep K G) (d n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if d ≤ finrank K (V i) then 1 else 0

private theorem largeFactorCount_zero (V : ℕ → FDRep K G) (d : ℕ) : largeFactorCount V d 0 = 0 := by
  simp [largeFactorCount]

private theorem largeFactorCount_succ (V : ℕ → FDRep K G) (d n : ℕ) :
    largeFactorCount V d (n + 1) = largeFactorCount V d n +
      if d ≤ finrank K (V n) then 1 else 0 := by
  exact Finset.sum_range_succ _ _

/-- The tensor prefix of nonzero finite-dimensional spaces has positive dimension. -/
theorem finrank_tensorPrefix_pos (V : ℕ → FDRep K G)
    (hpos : ∀ i, 0 < finrank K (V i)) (n : ℕ) : 0 < finrank K (tensorPrefix V n) := by
  rw [finrank_tensorPrefix]
  exact Finset.prod_pos (fun i _ => hpos i)

/-- One rank contribution and the other large dimensions give the exponential bound. -/
theorem tensorPrefix_displacement_ge_pow [CharP K 2] (V : ℕ → FDRep K G)
    (t : G) (ht : t ^ 2 = 1) (d b : ℕ)
    (hpos : ∀ i, 0 < finrank K (V i))
    (hrank : ∀ i, d ≤ finrank K (V i) → b ≤ operatorFixedCodim ((V i).ρ t))
    (n : ℕ) (hc : 0 < largeFactorCount V d n) :
    b * d ^ (largeFactorCount V d n - 1) ≤ operatorFixedCodim ((tensorPrefix V n).ρ t) := by
  induction n with
  | zero => simp [largeFactorCount_zero] at hc
  | succ n ih =>
    have hl := mul_finrank_le_tprod_displacement_left (tensorPrefix V n).ρ (V n).ρ t ht
    have hr := mul_finrank_le_tprod_displacement_right (tensorPrefix V n).ρ (V n).ρ t ht
    change b * d ^ (largeFactorCount V d (n + 1) - 1) ≤
      operatorFixedCodim (Representation.tprod (tensorPrefix V n).ρ (V n).ρ t)
    rw [largeFactorCount_succ] at hc ⊢
    by_cases hdim : d ≤ finrank K (V n)
    · rw [if_pos hdim] at hc ⊢
      by_cases hz : largeFactorCount V d n = 0
      · rw [hz]
        simp only [zero_add, Nat.sub_self, pow_zero, mul_one]
        exact (hrank n hdim).trans
          ((Nat.le_mul_of_pos_left _ (finrank_tensorPrefix_pos V hpos n)).trans hr)
      · have hn : 0 < largeFactorCount V d n := Nat.pos_of_ne_zero hz
        simp only [Nat.add_sub_cancel]
        calc
          b * d ^ largeFactorCount V d n = (b * d ^ (largeFactorCount V d n - 1)) * d := by
            rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
          _ ≤ operatorFixedCodim ((tensorPrefix V n).ρ t) * finrank K (V n) :=
            Nat.mul_le_mul (ih hn) hdim
          _ ≤ _ := hl
    · rw [if_neg hdim, add_zero] at hc ⊢
      exact (ih hc).trans ((Nat.le_mul_of_pos_right _ (hpos n)).trans hl)

/-- A positive count is bounded by this power of any integer at least two. -/
theorem le_pow_pred {d c : ℕ} (hd : 2 ≤ d) (hc : 0 < c) : c ≤ d ^ (c - 1) := by
  induction c, hc using Nat.le_induction with
  | base => simp
  | succ c hc ih =>
    simp only [Nat.add_sub_cancel]
    calc
      c + 1 ≤ c * d := by nlinarith
      _ ≤ d ^ (c - 1) * d := Nat.mul_le_mul_right d ih
      _ = d ^ c := by rw [← pow_succ, Nat.sub_add_cancel hc]

/-- Each large factor contributes to a linear lower bound for the actual tensor. -/
theorem tensorPrefix_displacement_ge_count [CharP K 2] (V : ℕ → FDRep K G)
    (t : G) (ht : t ^ 2 = 1) (d b : ℕ) (hd : 2 ≤ d)
    (hpos : ∀ i, 0 < finrank K (V i))
    (hrank : ∀ i, d ≤ finrank K (V i) → b ≤ operatorFixedCodim ((V i).ρ t)) (n : ℕ) :
    b * largeFactorCount V d n ≤ operatorFixedCodim ((tensorPrefix V n).ρ t) := by
  by_cases hz : largeFactorCount V d n = 0
  · simp [hz]
  · have hc := Nat.pos_of_ne_zero hz
    exact (Nat.mul_le_mul_left b (le_pow_pred hd hc)).trans
      (tensorPrefix_displacement_ge_pow V t ht d b hpos hrank n hc)

end ReeF4.FixedSpaceEstimate
