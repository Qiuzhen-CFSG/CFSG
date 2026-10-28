module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.Generators
public import Mathlib.Algebra.Field.ZMod

/-!
# Generation of the full trio quotient coordinates

The two octad permutations cover S₃. Conjugating the elementary matrix by
the coordinate cycle, and taking products of these conjugates, gives all
six elementary transvections in SL₃(2). The displayed short words are
checked by kernel reduction. Gaussian elimination then gives every special
linear matrix: over F₂ the only nonzero diagonal coefficient is one.

The induction principle uses positive words, so lifting the four generators
and closing under multiplication suffices to lift the whole product.

Source context: the S₃ × L₃(2) quotient in Aschbacher, *Sporadic Groups*,
Chapter 7, Lemma 20.2(2), printed p.97. The generation argument uses Mathlib's
special-linear diagonal/transvection induction theorem.
-/

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction.AffineLiftConstruction

private def transvectionWord : Fin 3 → Fin 3 → List (Fin 4) :=
  ![![[], [3], [2, 3, 2, 2, 3, 2, 3, 2, 2, 3]],
    ![[2, 3, 2, 3, 2, 2, 3, 2, 3, 2], [], [2, 3, 2, 2]],
    ![[2, 2, 3, 2], [2, 2, 3, 2, 3, 2, 2, 3, 2, 3], []]]

private theorem transvectionWord_spec (i j : Fin 3) (hij : i ≠ j) :
    ((transvectionWord i j).map generatorQuotient).prod =
      (1, Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2)) := by
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | decide +kernel +revert

private def permutationWord : Fin 6 → List (Fin 4) :=
  ![[], [0], [1], [1,1], [0,1], [0,1,1]]

private theorem permutationWord_covers (s : Equiv.Perm (Fin 3)) :
    ∃ k, ((permutationWord k).map generatorQuotient).prod = (s, 1) := by
  revert s
  decide +kernel

/-- The four prescribed coordinate generators generate S₃ × SL₃(2)
using multiplication alone. -/
public theorem quotient_induction (P : QuotientModel → Prop) (h1 : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b))
    (hgen : ∀ k, P (generatorQuotient k)) (q : QuotientModel) : P q := by
  have hw (w : List (Fin 4)) : P (w.map generatorQuotient).prod := by
    induction w with
    | nil => exact h1
    | cons k w ih => exact hmul _ _ (hgen k) ih
  have hs (s : Equiv.Perm (Fin 3)) : P (s, 1) := by
    obtain ⟨k, hk⟩ := permutationWord_covers s
    rw [← hk]
    exact hw _
  have hl (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : P (1, A) := by
    refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (ι := Fin 3) (F := ZMod 2) (fun A => P (1, A)) A ?_ ?_ ?_
    · intro i j hij c hc
      have hc1 : c = 1 := (show c = 0 ∨ c = 1 from by revert c; decide).resolve_left hc
      subst c
      have hd : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
        apply Subtype.ext
        simp [Matrix.SpecialLinearGroup.diag2n_coe]
      simpa only [hd, Prod.mk_one_one] using h1
    · intro i j hij a
      have ha : a = 0 ∨ a = 1 := by revert a; decide
      rcases ha with rfl | rfl
      · simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero, Prod.mk_one_one] using h1
      · rw [← transvectionWord_spec i j hij]
        exact hw _
    · intro A B hA hB
      exact hmul (1, A) (1, B) hA hB
  simpa only [Prod.mk_mul_mk, mul_one, one_mul] using hmul (q.1, 1) (1, q.2) (hs q.1) (hl q.2)

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction.AffineLiftConstruction
