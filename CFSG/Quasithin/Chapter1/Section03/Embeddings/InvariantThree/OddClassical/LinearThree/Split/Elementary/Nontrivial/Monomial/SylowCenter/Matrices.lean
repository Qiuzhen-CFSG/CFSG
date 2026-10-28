module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Monomial.SylowCenter.Coordinates

/-!
# Diagonal Sylow-center elements and a coordinate-sign centralizer

A diagonal lift commuting projectively with a monomial transposition commutes
linearly with it: the fixed coordinate, whose entries are nonzero, forces the
scalar discrepancy to be one. Its entries on the two moved coordinates are
therefore equal. Such a diagonal matrix centralizes every matrix commuting
with the sign of the fixed coordinate, since those matrices preserve the
one-plus-two coordinate decomposition.

Source: the split decomposition stabilizer of GLS3, Theorem 6.5.3(b),
`refs/KGroup/GLS3/chapter6.tex`, used in Aschbacher–Smith, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

public section

open Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial.Monomial.SylowCenter

open Matrix.SL3.SplitMonomial Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable {F : Type*} [Field F]

private theorem projection_eq_scalar (u v : SL(3,F))
    (h : Matrix.PSL3.projection F u = Matrix.PSL3.projection F v) :
    ∃ r : F, u.val = r • v.val := by
  have hc := (Matrix.PSL3.projection F).eq_iff.mp h
  rw [Matrix.PSL3.projection_ker] at hc
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    u.val = (v * (v⁻¹ * u)).val := by simp only [mul_inv_cancel_left]
    _ = v.val * Matrix.scalar (Fin 3) r := by rw [Matrix.SpecialLinearGroup.coe_mul, ← hr]
    _ = r • v.val := by ext i j; simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

private theorem entry_ne_zero_of_support (g : SL(3,F)) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ i j, i ≠ σ j → g i j = 0) (j : Fin 3) : g (σ j) j ≠ 0 := by
  intro hn
  have hz (i : Fin 3) : g i j = 0 := by
    by_cases hi : i = σ j
    · simpa [hi] using hn
    · exact hσ i j hi
  have hh := congrArg (fun A : SL(3,F) => A j j) (inv_mul_cancel g)
  change (g⁻¹.val * g.val) j j = (1 : Matrix (Fin 3) (Fin 3) F) j j at hh
  simp only [Matrix.one_apply_eq, Matrix.mul_apply, hz, mul_zero, Finset.sum_const_zero] at hh
  exact zero_ne_one hh

/-- The projective coordinate action determines the support of every monomial lift. -/
theorem support_of_coordinateAction (h2 : (2 : F) ≠ 0) (g : linear F) (t : projective F)
    (ht : Matrix.PSL3.projection F g.val = t.val) :
    ∀ i j, i ≠ coordinateAction h2 t j → g.val i j = 0 := by
  obtain ⟨σ, hσ⟩ := exists_column_permutation g
  have hs (k : Fin 3) : g.val * signSL k * g.val⁻¹ = signSL (σ k) := by
    apply mul_inv_eq_iff_eq_mul.mpr
    apply Subtype.ext
    change g.val.val * Matrix.diagonal _ = Matrix.diagonal _ * g.val.val
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : i = σ j
    · subst i
      by_cases hjk : j = k
      · subst j; simp
      · simp [hjk, σ.injective.ne hjk]
    · change g.val i j * _ = _ * g.val i j
      rw [hσ i j hij, zero_mul, mul_zero]
  have he (k : Fin 3) : σ k = coordinateAction h2 t k := by
    apply signElement_injective h2
    have hh := congrArg (Matrix.PSL3.projection F) (hs k)
    rw [map_mul, map_mul, map_inv, ht] at hh
    exact hh.symm.trans (coordinateAction_spec h2 t k)
  intro i j hij
  exact hσ i j (by simpa only [he] using hij)

/-- Commutation with a projective transposition forces equality on its two moved coordinates.
The fixed coordinate removes the scalar ambiguity. -/
theorem repeated_diagonal_of_transposition (D g : SL(3,F)) (k : Fin 3)
    (hD : D.val = Matrix.diagonal (fun i => D i i))
    (hg : ∀ i j, i ≠ swapPerm k j → g i j = 0)
    (hc : Commute (Matrix.PSL3.projection F D) (Matrix.PSL3.projection F g)) :
    ∀ i j, i ≠ k → j ≠ k → D i i = D j j := by
  have hd (i : Fin 3) : D i i ≠ 0 := by
    apply entry_ne_zero_of_support D 1
    intro r s hrs
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M r s) hD
    have hrs' : r ≠ s := hrs
    simpa [Matrix.diagonal_apply, hrs'] using h
  obtain ⟨r, hr⟩ := projection_eq_scalar (D*g) (g*D) (by simpa only [map_mul] using hc.eq)
  have he (i j : Fin 3) : D i i * g i j = r * (g i j * D j j) := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) hr
    change (D.val * g.val) i j = r * ((g.val * D.val) i j) at h
    rw [hD, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    exact h
  have hgk : g k k ≠ 0 := by simpa only [swapPerm_fix] using entry_ne_zero_of_support g _ hg k
  have hr1 : r = 1 := by
    apply mul_right_cancel₀ (mul_ne_zero (hd k) hgk)
    simpa only [one_mul, mul_comm (g k k) (D k k)] using (he k k).symm
  have hp (j : Fin 3) : D (swapPerm k j) (swapPerm k j) = D j j := by
    apply mul_right_cancel₀ (entry_ne_zero_of_support g _ hg j)
    simpa only [hr1, one_mul, mul_comm (g (swapPerm k j) j) (D j j)] using he (swapPerm k j) j
  intro i j hi hj
  have hcases : i = j ∨ i = swapPerm k j := by
    have h : ∀ k i j : Fin 3, i ≠ k → j ≠ k → i = j ∨ i = swapPerm k j := by decide
    exact h k i j hi hj
  rcases hcases with rfl | rfl
  · rfl
  · exact hp j

/-- A diagonal matrix scalar on the two-coordinate block centralizes the whole sign centralizer. -/
theorem commute_of_repeated_diagonal (h2 : (2 : F) ≠ 0) (D x : SL(3,F)) (k : Fin 3)
    (hD : D.val = Matrix.diagonal (fun i => D i i))
    (hd : ∀ i j, i ≠ k → j ≠ k → D i i = D j j)
    (hx : Commute x (signSL k)) : Commute D x := by
  apply Subtype.ext
  change D.val * x.val = x.val * D.val
  rw [hD]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hc := congrArg (fun A : SL(3,F) => A i j) hx.eq
  change (x.val * Matrix.diagonal (fun r => if r = k then (1 : F) else -1)) i j =
    (Matrix.diagonal (fun r => if r = k then (1 : F) else -1) * x.val) i j at hc
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  by_cases hi : i = k <;> by_cases hj : j = k
  · subst i; subst j; exact mul_comm _ _
  · simp only [if_pos hi, if_neg hj, mul_neg, mul_one, one_mul] at hc
    have hz : x i j = 0 :=
      (mul_eq_zero.mp (show (2 : F) * x i j = 0 by linear_combination -hc)).resolve_left h2
    simp [hz]
  · simp only [if_neg hi, if_pos hj, neg_mul, mul_one, one_mul] at hc
    have hz : x i j = 0 :=
      (mul_eq_zero.mp (show (2 : F) * x i j = 0 by linear_combination hc)).resolve_left h2
    simp [hz]
  · rw [hd i j hi hj, mul_comm]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial.Monomial.SylowCenter
