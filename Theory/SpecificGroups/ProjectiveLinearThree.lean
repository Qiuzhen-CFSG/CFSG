module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Tactic.FinCases
/-!
# Elements of order three in projective special linear groups

The companion matrix of X² + X + 1 has determinant one and cube one.
Adjoining an identity block gives an element of every dimension at least two.
Its off-diagonal entry one prevents it from being scalar, so it survives the
central quotient with order three. Lagrange's theorem gives three-divisibility,
without a field-order formula or a simplicity assumption.

Source application: Aschbacher--Smith, 1.1.5(3) and 15.3.34,
`refs/quasithin.pdf`, printed pp.501--502 and 1134.
-/

public section

open Matrix
open scoped MatrixGroups
namespace Matrix.ProjectiveSpecialLinearGroup
variable (F : Type*) [Field F]
private def cubeLift : SL(2,F) :=
  ⟨!![-1, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
private theorem cubeLift_cube : cubeLift F ^ 3 = 1 := by
  apply Subtype.ext
  change (cubeLift F).val ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubeLift, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

private def extend (k : ℕ) : SL(2,F) →* SpecialLinearGroup (Fin 2 ⊕ Fin k) F where
  toFun A := ⟨Matrix.fromBlocks A.val 0 0 1, by simp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' A B := by
    apply Subtype.ext
    change Matrix.fromBlocks (A.val * B.val) 0 0 (1 : Matrix (Fin k) (Fin k) F) =
      Matrix.fromBlocks A.val 0 0 1 * Matrix.fromBlocks B.val 0 0 1
    simp [Matrix.fromBlocks_multiply]

private def reindex (k : ℕ) :
    SpecialLinearGroup (Fin 2 ⊕ Fin k) F →* SL(2 + k,F) where
  toFun A := ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv A.val, by
    rw [Matrix.det_reindex_self]; exact A.property⟩
  map_one' := by apply Subtype.ext; exact map_one (Matrix.reindexRingEquiv F finSumFinEquiv)
  map_mul' A B := by apply Subtype.ext; exact map_mul (Matrix.reindexRingEquiv F finSumFinEquiv) A.val B.val

/-- A nontrivial cubic element survives the scalar central quotient. -/
theorem exists_orderOf_eq_three (n : ℕ) (hn : 2 ≤ n) :
    ∃ x : PSL(n,F), orderOf x = 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  let A := reindex F k (extend F k (cubeLift F))
  let q := QuotientGroup.mk' (Subgroup.center SL(2+k,F))
  refine ⟨q A, orderOf_eq_prime ?_ ?_⟩
  · dsimp only [A]
    rw [← map_pow, ← map_pow, ← map_pow, cubeLift_cube, map_one, map_one, map_one]
  · intro h
    obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
      ((QuotientGroup.eq_one_iff _).mp h)
    have hh := congrArg (fun M : Matrix (Fin (2+k)) (Fin (2+k)) F =>
      M (finSumFinEquiv (Sum.inl 1)) (finSumFinEquiv (Sum.inl 0))) hr
    change (Matrix.scalar (Fin (2+k)) r)
      (finSumFinEquiv (Sum.inl 1)) (finSumFinEquiv (Sum.inl 0)) =
        (Matrix.fromBlocks !![-1,-1;1,0] 0 0 (1 : Matrix (Fin k) (Fin k) F))
          (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl 1)))
          (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl 0))) at hh
    simp [Matrix.scalar, Matrix.diagonal] at hh

/-- Three divides the order in every dimension at least two. -/
theorem three_dvd_card (n : ℕ) (hn : 2 ≤ n) : 3 ∣ Nat.card PSL(n,F) := by
  obtain ⟨x, hx⟩ := exists_orderOf_eq_three F n hn
  simpa only [hx] using orderOf_dvd_natCard x
end Matrix.ProjectiveSpecialLinearGroup
