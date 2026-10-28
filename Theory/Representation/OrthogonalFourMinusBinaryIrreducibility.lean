module
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Geometry
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Faithfulness
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Binary irreducibility of the finite Hermitian module

Every additive subgroup of the Hermitian two-by-two matrices invariant under
SL₂ over GF(2^(2n)) is zero or the whole space. Two upper-transvection
differences extract a nonzero diagonal matrix. Nontriviality of the quadratic
Frobenius also handles a vector with both diagonal entries zero. Diagonal
conjugation, bijectivity of squaring in the fixed field, and the opposite
transvection then generate every Hermitian matrix additively.

The proof requires no scalar closure of the subgroup and includes n=1.
The multiplicative action is the literal existing matrix representation.
This supplies the irreducibility clause of Aschbacher--Smith C.1.7 for the
plane local in F.1.12(I)(6), printed pp.123 and 263–264 of
`refs/quasithin.pdf` (combined manuscript, 1 March 2004).
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.FiniteModel
namespace BinaryIrreducibility
open Matrix Matrix.SpecialLinearGroup
variable (n : ℕ) [NeZero n]

private abbrev upper (t : Field n) : SpecialLinearGroup (Fin 2) (Field n) :=
  transvection zero_ne_one t

private def swap : SpecialLinearGroup (Fin 2) (Field n) :=
  ⟨!![0,1;1,0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private def diagonal (a : fixedField n) : Space n := (coordinates n).symm ((a,0),0)

private def difference (t : Field n) (X : Space n) : Space n :=
  action n (upper n t) X - X

private theorem difference_val (t : Field n) (X : Space n) :
    (difference n t X).val =
      !![t * X.val 1 0 + conjugation n t * X.val 0 1 +
          t * conjugation n t * X.val 1 1, t * X.val 1 1;
        conjugation n t * X.val 1 1, 0] := by
  change (action n (upper n t) X).val - X.val = _
  rw [action_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, transvection_coe, adjoint, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem double_difference_val (s t : Field n) (X : Space n) :
    (difference n s (difference n t X)).val =
      !![(s * conjugation n t + conjugation n s * t) * X.val 1 1, 0; 0, 0] := by
  rw [difference_val, difference_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_mul, mul_assoc]

private theorem swap_val (X : Space n) :
    (action n (swap n) X).val = !![X.val 1 1, X.val 1 0; X.val 0 1, X.val 0 0] := by
  rw [action_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap, adjoint, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem diagonal_of_entries (X : Space n)
    (h01 : X.val 0 1 = 0) (h10 : X.val 1 0 = 0) (h11 : X.val 1 1 = 0) :
    X = diagonal n ⟨X.val 0 0, entry_fixed n X 0⟩ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, coordinates_symm_val, h01, h10, h11]

omit [NeZero n] in
private theorem add_conjugate_ne_zero (t : Field n) (ht : conjugation n t ≠ t) :
    t + conjugation n t ≠ 0 := by
  intro h
  apply ht
  have : conjugation n t = -t := (eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm] using h)
  simpa only [CharTwo.neg_eq] using this

private theorem diagonal_mem_of_bottom_ne_zero
    (W : AddSubgroup (Space n))
    (hW : ∀ (A : SpecialLinearGroup (Fin 2) (Field n)) (X : Space n), X ∈ W → action n A X ∈ W)
    (X : Space n) (hX : X ∈ W) (hb : X.val 1 1 ≠ 0) :
    ∃ a : fixedField n, a ≠ 0 ∧ diagonal n a ∈ W := by
  obtain ⟨t, ht⟩ := exists_conjugation_ne n
  let Y := difference n t (difference n 1 X)
  have hY : Y ∈ W := W.sub_mem (hW _ _ (W.sub_mem (hW _ _ hX) hX))
    (W.sub_mem (hW _ _ hX) hX)
  have hv : Y.val = !![(t + conjugation n t) * X.val 1 1, 0;0,0] := by
    simpa [Y] using double_difference_val n t 1 X
  refine ⟨⟨Y.val 0 0, entry_fixed n Y 0⟩, ?_, ?_⟩
  · intro ha
    have hz := congrArg Subtype.val ha
    change Y.val 0 0 = 0 at hz
    rw [hv] at hz
    exact (mul_ne_zero (add_conjugate_ne_zero n t ht) hb) hz
  · rw [← diagonal_of_entries n Y (by simp [hv]) (by simp [hv]) (by simp [hv])]
    exact hY

private theorem exists_diagonal_mem
    (W : AddSubgroup (Space n))
    (hW : ∀ (A : SpecialLinearGroup (Fin 2) (Field n)) (X : Space n), X ∈ W → action n A X ∈ W)
    (X : Space n) (hX : X ∈ W) (hne : X ≠ 0) :
    ∃ a : fixedField n, a ≠ 0 ∧ diagonal n a ∈ W := by
  by_cases hb : X.val 1 1 = 0
  · by_cases ha : X.val 0 0 = 0
    · have hz : X.val 0 1 ≠ 0 := by
        intro hz
        apply hne
        apply Subtype.ext
        have hz' : X.val 1 0 = 0 := by rw [← entry_conjugate n X 1 0, hz, map_zero]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha, hb, hz, hz']
      obtain ⟨t, ht⟩ := exists_conjugation_ne n
      let Y := difference n (t * X.val 0 1) X
      have hY : Y ∈ W := W.sub_mem (hW _ _ hX) hX
      have hy : Y.val 0 0 =
          (t + conjugation n t) * X.val 0 1 * conjugation n (X.val 0 1) := by
        rw [show Y.val = _ from difference_val n (t * X.val 0 1) X]
        simp only [Matrix.of_apply, Matrix.cons_val_zero, hb, mul_zero, add_zero, map_mul]
        rw [← entry_conjugate n X 1 0]
        ring
      apply diagonal_mem_of_bottom_ne_zero n W hW (action n (swap n) Y) (hW _ _ hY)
      rw [swap_val]
      change Y.val 0 0 ≠ 0
      rw [hy]
      exact mul_ne_zero (mul_ne_zero (add_conjugate_ne_zero n t ht) hz)
        ((map_ne_zero (conjugation n)).mpr hz)
    · apply diagonal_mem_of_bottom_ne_zero n W hW (action n (swap n) X) (hW _ _ hX)
      simpa [swap_val] using ha
  · exact diagonal_mem_of_bottom_ne_zero n W hW X hX hb


private theorem diagonal_action (c a : fixedField n) (hc : (c : Field n) ≠ 0) :
    action n (diag2 (c : Field n) hc) (diagonal n a) = diagonal n (c ^ 2 * a) := by
  apply Subtype.ext
  rw [action_apply]
  have hcfix : conjugation n (c : Field n) = c := c.property
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, coordinates_symm_val, diag2_coe', adjoint, Matrix.mul_apply,
      Fin.sum_univ_two, hcfix, pow_two]
  ring

private theorem all_diagonal_mem
    (W : AddSubgroup (Space n))
    (hW : ∀ (A : SpecialLinearGroup (Fin 2) (Field n)) (X : Space n), X ∈ W → action n A X ∈ W)
    (a : fixedField n) (ha : a ≠ 0) (hWa : diagonal n a ∈ W) (b : fixedField n) :
    diagonal n b ∈ W := by
  by_cases hb : b = 0
  · subst b
    have hz : diagonal n 0 = 0 := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [diagonal]
    rw [hz]
    exact W.zero_mem
  · obtain ⟨c, hc⟩ := (Finite.surjective_of_injective
      (CharTwo.sq_injective (R := fixedField n))) (b / a)
    change c ^ 2 = b / a at hc
    have hc0 : c ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at hc; exact (div_ne_zero hb ha) hc.symm
    have hc0' : (c : Field n) ≠ 0 := fun h => hc0 (Subtype.ext h)
    have he : c ^ 2 * a = b := by rw [hc, div_mul_cancel₀ _ ha]
    rw [← he, ← diagonal_action n c a hc0']
    exact hW _ _ hWa

private def bottom (a : fixedField n) : Space n := (coordinates n).symm ((0,a),0)
private def offDiagonal (z : Field n) : Space n := (coordinates n).symm ((0,0),z)

private theorem swap_diagonal (a : fixedField n) :
    action n (swap n) (diagonal n a) = bottom n a := by
  apply Subtype.ext
  rw [swap_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, bottom]

private theorem offDiagonal_eq (z : Field n) :
    offDiagonal n z = difference n z (bottom n 1) - diagonal n (norm n z) := by
  apply Subtype.ext
  change (offDiagonal n z).val = (difference n z (bottom n 1)).val - (diagonal n (norm n z)).val
  rw [difference_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [offDiagonal, bottom, diagonal, norm]

private theorem decomposition (X : Space n) :
    X = diagonal n (coordinates n X).1.1 + bottom n (coordinates n X).1.2 +
      offDiagonal n (coordinates n X).2 := by
  apply (coordinates n).injective
  simp [diagonal, bottom, offDiagonal, Prod.ext_iff]

/-- Every additive subgroup invariant under all SL₂ congruences is zero or the whole
Hermitian space. In particular this is irreducibility over the binary prime field. -/
theorem invariant_addSubgroup_eq_bot_or_top
    (W : AddSubgroup (Space n))
    (hW : ∀ (A : SpecialLinearGroup (Fin 2) (Field n)) (X : Space n), X ∈ W → action n A X ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨X, hX, hne⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hbot)
  have hne' : X ≠ 0 := by simpa only [AddSubgroup.mem_bot] using hne
  obtain ⟨a, ha, hWa⟩ := exists_diagonal_mem n W hW X hX hne'
  have hd := all_diagonal_mem n W hW a ha hWa
  have hb (b : fixedField n) : bottom n b ∈ W := by
    rw [← swap_diagonal]
    exact hW _ _ (hd b)
  have ho (z : Field n) : offDiagonal n z ∈ W := by
    rw [offDiagonal_eq]
    exact W.sub_mem (W.sub_mem (hW _ _ (hb 1)) (hb 1)) (hd _)
  apply top_unique
  intro Y _
  rw [decomposition n Y]
  exact W.add_mem (W.add_mem (hd _) (hb _)) (ho _)
end BinaryIrreducibility

variable (n : ℕ) [NeZero n]

/-- The same Hermitian representation, written as an action on the multiplicative
additive group. -/
def multiplicativeAction : Matrix.SpecialLinearGroup (Fin 2) (Field n) →*
    MulAut (Multiplicative (Space n)) where
  toFun A := (linearActionHom n A).toAddEquiv.toMultiplicative
  map_one' := by
    ext X : 1
    change action n 1 X.toAdd = X.toAdd
    rw [map_one]
    rfl
  map_mul' A B := by
    ext X : 1
    change action n (A * B) X.toAdd = action n A (action n B X.toAdd)
    rw [map_mul]
    rfl

@[simp] theorem multiplicativeAction_apply (A : Matrix.SpecialLinearGroup (Fin 2) (Field n))
    (X : Multiplicative (Space n)) :
    (multiplicativeAction n A X).toAdd = action n A X.toAdd := rfl

/-- Irreducibility for arbitrary invariant subgroups, with no scalar-closure
assumption. -/
theorem multiplicativeAction_irreducible (W : Subgroup (Multiplicative (Space n)))
    (hW : ∀ A X, X ∈ W → multiplicativeAction n A X ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let W' : AddSubgroup (Space n) := {
    carrier := {X | Multiplicative.ofAdd X ∈ W}
    zero_mem' := W.one_mem
    add_mem' := fun hx hy => W.mul_mem hx hy
    neg_mem' := fun hx => W.inv_mem hx }
  have hi := BinaryIrreducibility.invariant_addSubgroup_eq_bot_or_top n W'
    (fun A X hX => hW A (Multiplicative.ofAdd X) hX)
  rcases hi with h | h
  · left
    apply W.eq_bot_iff_forall.mpr
    intro X hX
    have : X.toAdd ∈ W' := hX
    rw [h, AddSubgroup.mem_bot] at this
    exact Multiplicative.toAdd.injective this
  · right
    apply top_unique
    intro X _
    show X.toAdd ∈ W'
    rw [h]
    trivial
end Representation.OrthogonalFourMinus.FiniteModel
