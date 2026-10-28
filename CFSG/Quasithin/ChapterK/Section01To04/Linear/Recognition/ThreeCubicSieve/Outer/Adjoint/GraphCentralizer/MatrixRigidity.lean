module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Forms
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.SymmetricForms.BinaryTernary
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Scalar rigidity and graph involutions on trace-zero ternary matrices

Commuting with the off-diagonal matrix units forces a matrix to be scalar.
Thus an involutory inner action has a determinant-one representative, obtained
by a scalar correction without choosing a cube root. An involutory graph action
has symmetric conjugating matrix in characteristic two. The existing finite
binary ternary congruence theorem then normalizes it to the literal Gram matrix
used by `Adjoint.graphCoordinates`, including the fields of orders two and four.

These are matrix ingredients for the simultaneous elementary actor reduction.
They do not assert the remaining graph-centralizer root-group placement.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
open Matrix
variable {F : Type*} [Field F]
abbrev Mat := Matrix (Fin 3) (Fin 3) F

def inner (g : GL (Fin 3) F) (X : Mat (F := F)) := g.val * X * (g⁻¹).val

def graph (g : GL (Fin 3) F) (X : Mat (F := F)) := inner g X.transpose

lemma scalar_of_centralizes_traceZero (M : Mat (F := F))
    (h : ∀ X : Mat (F := F), X.trace = 0 → M * X = X * M) :
    ∃ c : F, M = Matrix.scalar (Fin 3) c := by
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
    (M := M) (fun i j hij => (h _ (Matrix.trace_single_eq_of_ne i j 1 hij)).symm)
  exact ⟨c, hc.symm⟩

lemma scalar_of_inner_eq_id (g : GL (Fin 3) F)
    (h : ∀ X : Mat (F := F), X.trace = 0 → inner g X = X) :
    ∃ c : F, g.val = Matrix.scalar (Fin 3) c := by
  apply scalar_of_centralizes_traceZero
  intro X hX
  have hh := congrArg (fun Y => Y * g.val) (h X hX)
  simpa only [inner, Matrix.mul_assoc, g.inv_mul, Matrix.mul_one] using hh

lemma inner_mul (g h : GL (Fin 3) F) (X : Mat (F := F)) :
    inner (g * h) X = inner g (inner h X) := by
  simp [inner, mul_assoc]

lemma inner_square_scalar (g : GL (Fin 3) F)
    (h : ∀ X : Mat (F := F), X.trace = 0 → inner g (inner g X) = X) :
    ∃ c : F, g.val * g.val = Matrix.scalar (Fin 3) c := by
  exact scalar_of_inner_eq_id (g * g) (fun X hX => by rw [inner_mul]; exact h X hX)

/-- An involutory projective conjugation in odd dimension three has an actual
special-linear representative. The formula removes diagonal ambiguity even
when the field has nontrivial cube roots of unity. -/
theorem det_one_involution_representative (g : GL (Fin 3) F)
    (h : ∀ X : Mat (F := F), X.trace = 0 → inner g (inner g X) = X) :
    ∃ s : SL(3,F), s ^ 2 = 1 ∧
      ∀ X : Mat (F := F), inner (SpecialLinearGroup.toGL s) X = inner g X := by
  obtain ⟨c, hc⟩ := inner_square_scalar g h
  have hd : g.val.det ≠ 0 := GeneralLinearGroup.det_ne_zero g
  have hd2 : g.val.det ^ 2 = c ^ 3 := by
    have he := congrArg Matrix.det hc
    simpa [Matrix.det_mul, Matrix.scalar, Matrix.det_diagonal, Fin.prod_univ_three, pow_two, pow_succ] using he
  have hc0 : c ≠ 0 := by
    intro hz
    simp [hz, hd] at hd2
  let u : Fˣ := Units.mk0 (c / g.val.det) (div_ne_zero hc0 hd)
  let k : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) u * g
  have hk : k.val.det = 1 := by
    change (Matrix.scalar (Fin 3) (c / g.val.det) * g.val).det = 1
    simp only [Matrix.det_mul, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, div_pow]
    rw [← hd2]
    field_simp
  let s : SL(3,F) := ⟨k.val, hk⟩
  have hs : SpecialLinearGroup.toGL s = k := Units.ext rfl
  have hsq : s ^ 2 = 1 := by
    apply Subtype.ext
    simp only [pow_two]
    change k.val * k.val = 1
    change (Matrix.scalar (Fin 3) (c / g.val.det) * g.val) *
      (Matrix.scalar (Fin 3) (c / g.val.det) * g.val) = 1
    simp only [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
    have hcd : (c / g.val.det * (c / g.val.det)) * c = 1 := by
      field_simp
      simpa only [pow_two, pow_succ, pow_one] using hd2.symm
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.scalar, Matrix.smul_apply, smul_eq_mul] using hcd
    · simp [hij, Matrix.smul_apply]
  refine ⟨s, hsq, fun X => ?_⟩
  rw [hs, inner_mul]
  simp only [inner, GeneralLinearGroup.coe_scalar, ← map_inv, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, ← Matrix.smul_eq_mul_diagonal, smul_smul,
    Units.inv_mul, one_smul]

/-- The determinant-one representative preserves the operator on every matrix. -/
theorem det_one_representative (g : GL (Fin 3) F)
    (h : ∀ X : Mat (F := F), X.trace = 0 → inner g (inner g X) = X) :
    ∃ s : SL(3,F), ∀ X : Mat (F := F), inner (SpecialLinearGroup.toGL s) X = inner g X := by
  obtain ⟨s, _, hs⟩ := det_one_involution_representative g h
  exact ⟨s, hs⟩

lemma graph_square_symmetric [CharP F 2] (g : GL (Fin 3) F)
    (h : ∀ X : Mat (F := F), X.trace = 0 → graph g (graph g X) = X) :
    g.val.transpose = g.val := by
  let k : GL (Fin 3) F := {
    val := g.val * (g⁻¹).val.transpose
    inv := g.val.transpose * (g⁻¹).val
    val_inv := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g⁻¹).val.transpose,
        ← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one, Matrix.one_mul, g.mul_inv]
    inv_val := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g⁻¹).val,
        g.inv_mul, Matrix.one_mul, ← Matrix.transpose_mul, g.inv_mul, Matrix.transpose_one] }
  have hk : ∀ X : Mat (F := F), X.trace = 0 → inner k X = X := by
    intro X hX
    have hh := h X hX
    change (g.val * (g⁻¹).val.transpose) * X * (g.val.transpose * (g⁻¹).val) = X
    simpa only [graph, inner, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc] using hh
  obtain ⟨c, hc⟩ := scalar_of_inner_eq_id k hk
  have he : g.val = c • g.val.transpose := by
    have hh := congrArg (fun Y => Y * g.val.transpose) hc
    change (g.val * (g⁻¹).val.transpose) * g.val.transpose = _ at hh
    simpa only [Matrix.mul_assoc, ← Matrix.transpose_mul, g.mul_inv,
      Matrix.transpose_one, Matrix.mul_one, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] using hh
  have het : g.val.transpose = c • g.val := by
    simpa only [Matrix.transpose_smul, Matrix.transpose_transpose] using
      congrArg Matrix.transpose he
  have hc2 : c * c = 1 := by
    apply smul_left_injective F (Units.ne_zero g)
    change (c * c) • g.val = (1 : F) • g.val
    calc
      (c * c) • g.val = c • g.val.transpose := by rw [het, smul_smul]
      _ = g.val := he.symm
      _ = (1 : F) • g.val := (one_smul F _).symm
  have hc1 : c = 1 := by
    have hh : c ^ 2 = (1 : F) ^ 2 := by simpa only [pow_two, mul_one] using hc2
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hh with hh | hh
    · exact hh
    · simpa only [CharTwo.neg_eq] using hh
  simpa only [hc1, one_smul] using het

/-- A symmetric graph matrix can be normalized to the literal Gram matrix
used by `graphCoordinates`, over every finite binary field. -/
theorem symmetric_gram [Finite F] [CharP F 2] (g : GL (Fin 3) F)
    (hg : g.val.transpose = g.val) :
    ∃ C : GL (Fin 3) F, C.val * g.val * C.val.transpose = gram F := by
  obtain ⟨D, hD⟩ := Matrix.SymmetricTernary.exists_congruence_antidiagonal
    g.val hg (GeneralLinearGroup.det_ne_zero g)
  let P : Mat (F := F) := !![1,0,0; 0,0,1; 0,1,0]
  have hP : (P * D.val.transpose) * g.val * (P * D.val.transpose).transpose = gram F := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      P * D.val.transpose * g.val * (D.val * P.transpose) =
          P * (D.val.transpose * g.val * D.val) * P.transpose := by simp only [mul_assoc]
      _ = _ := by
        rw [hD]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [P, gram, Matrix.mul_apply, Fin.sum_univ_three]
  have hd : (P * D.val.transpose).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (by simp [P, Matrix.det_fin_three]) (GeneralLinearGroup.det_ne_zero D)
  exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, hP⟩

/-- The graph involution conjugacy for the actual trace-zero matrix action. -/
theorem graph_gram [Finite F] [CharP F 2] (g : GL (Fin 3) F)
    (h : ∀ X : Mat (F := F), X.trace = 0 → graph g (graph g X) = X) :
    ∃ C : GL (Fin 3) F, C.val * g.val * C.val.transpose = gram F :=
  symmetric_gram g (graph_square_symmetric g h)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
