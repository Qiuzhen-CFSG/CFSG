module

public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.Model
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Quasithin.CoprimeRank

/-!
# Split odd-prime rank in the actual degree-three linear groups

Two independent unit coordinates embed into the determinant-one diagonal
torus. If p divides the unit order, their product has p-rank at least two.
For p other than three the scalar center is p-prime, so the canonical SL₃
to PSL₃ quotient preserves this rank. The final theorem retains any supplied
component central-quotient marking, including a central two-kernel.

Source: Aschbacher–Smith, A.3.18, pp.51–53, in the rank-two application of
2.5.7, printed p.556. No simplicity or automorphism classification is used.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.SplitPrimeRank
open SylowFixedActions.Standard
variable (F : Type*) [Field F]

/-- The two unit coordinates of the original diagonal torus remain independent. -/
theorem diagonalSL_injective : Function.Injective (diagonalSL F) := by
  intro x y h
  apply Prod.ext
  · apply Units.ext
    have hh := congrArg (fun a : SL(3,F) => a.val 0 0) h
    simpa only [diagonalSL_val, Matrix.diagonal_apply_eq, Matrix.cons_val_zero] using hh
  · apply Units.ext
    have hh := congrArg (fun a : SL(3,F) => a.val 1 1) h
    simpa only [diagonalSL_val, Matrix.diagonal_apply_eq, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hh

variable [Finite F] {p : ℕ} [Fact p.Prime]

/-- Each prime dividing the split torus order gives rank at least two in SL₃. -/
theorem special_rank (hd : p ∣ Nat.card F - 1) : 2 ≤ primeRank p SL(3,F) := by
  have hu : 1 ≤ primeRank p Fˣ := by
    by_contra hh
    have hz : primeRank p Fˣ = 0 := by omega
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (by simpa only [Nat.card_units] using hd)
  have hi := primeRank_le_of_injective p (diagonalSL F) (diagonalSL_injective F)
  rw [primeRank_prod_eq_add] at hi
  omega

/-- The literal projective quotient preserves this rank away from its cubic center. -/
theorem projective_rank (hp : p ≠ 3) (hd : p ∣ Nat.card F - 1) :
    2 ≤ primeRank p PSL(3,F) := by
  have hc : Nat.Coprime p (Nat.card (projection F).ker) := by
    rw [projection_ker]
    apply Nat.Coprime.of_dvd_right (Matrix.SL3.card_center_dvd_three F)
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun h =>
      hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h))
  rw [← primeRank_eq_of_surjective_of_coprime p (projection F) (projection_surjective F) hc]
  exact special_rank F hd

/-- The same lower bound passes through the original p-prime central kernel. -/
theorem component_rank {H : Type*} [Group H] [Finite H] (L : Subgroup H)
    (hz : Nat.Coprime p (Nat.card (center L)))
    (e : L ⧸ center L ≃* PSL(3,F)) (hp : p ≠ 3) (hd : p ∣ Nat.card F - 1) :
    2 ≤ primeRank p L := by
  have hr := projective_rank F hp hd
  rw [← primeRank_congr p e] at hr
  exact hr.trans (primeRank_quotient_le_of_coprime p (center L) hz)

end Matrix.PSL3.SplitPrimeRank
