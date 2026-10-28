module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Forms
import Mathlib.Tactic.NoncommRing
/-!
# Eliminating scalar factors from adjoint involutions

Conjugation and conjugate-transpose preserve the trace pairing. A scalar times
one of these operators scales the pairing by the square of the scalar. If the
operator squares to one, evaluating the pairing on opposite matrix units
forces the fourth power of the scalar to be one. In characteristic two the
scalar is therefore one, without any lower bound on the field order.

Source: the actual adjoint operators in GM, Proposition 4.8, step 3A.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms
variable {F : Type*} [Field F]

abbrev mat (x : AdjointSpace F) : Matrix (Fin 3) (Fin 3) F := LinearMap.toMatrix' x.val

theorem conj_mul_conj (g : GL (Fin 3) F) (X Y : Matrix (Fin 3) (Fin 3) F) :
    (g.val * X * g.inv) * (g.val * Y * g.inv) = g.val * (X * Y) * g.inv := by
  calc
    _ = g.val * X * (g.inv * g.val) * Y * g.inv := by noncomm_ring
    _ = _ := by rw [g.inv_val, mul_one, mul_assoc g.val X Y]

theorem trace_pair_conj (g : GL (Fin 3) F) (X Y : Matrix (Fin 3) (Fin 3) F) :
    ((g.val * X * g.inv) * (g.val * Y * g.inv)).trace = (X * Y).trace := by
  rw [conj_mul_conj]
  exact Matrix.trace_units_conj g (X * Y)

theorem trace_pair_graph (g : GL (Fin 3) F) (X Y : Matrix (Fin 3) (Fin 3) F) :
    ((g.val * X.transpose * g.inv) * (g.val * Y.transpose * g.inv)).trace =
      (X * Y).trace := by
  rw [trace_pair_conj, ← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]

private def rootVector (i j : Fin 3) (h : i ≠ j) : AdjointSpace F :=
  ⟨(Matrix.single i j 1).toLin', by
    change LinearMap.trace F _ _ = 0
    rw [Matrix.trace_toLin'_eq]
    simp [Matrix.trace, h]⟩

private theorem trace_pair_roots :
    (mat (rootVector (F := F) 0 1 (by decide)) *
      mat (rootVector (F := F) 1 0 (by decide))).trace = 1 := by
  simp [mat, rootVector, Matrix.single_mul_single_same, Matrix.trace]

theorem scalar_eq_one_of_square [CharP F 2]
    (T : AdjointSpace F → AdjointSpace F) (hT : Function.Involutive T)
    (c : F) (g : GL (Fin 3) F)
    (hform : (∀ x, mat (T x) = c • (g.val * mat x * g.inv)) ∨
      (∀ x, mat (T x) = c • (g.val * (mat x).transpose * g.inv))) : c = 1 := by
  have hp (x y : AdjointSpace F) :
      (mat (T x) * mat (T y)).trace = c ^ 2 * (mat x * mat y).trace := by
    rcases hform with h | h
    · rw [h, h, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
        trace_pair_conj]
      simp only [smul_eq_mul, pow_two]
    · rw [h, h, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
        trace_pair_graph]
      simp only [smul_eq_mul, pow_two]
  have hh := hp (T (rootVector (F := F) 0 1 (by decide)))
    (T (rootVector (F := F) 1 0 (by decide)))
  rw [hT, hT, hp, trace_pair_roots, mul_one] at hh
  have hsq : c ^ 2 = 1 := by
    have he : (c ^ 2) ^ 2 = (1 : F) ^ 2 := by simpa [pow_two] using hh.symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hsq.trans (one_pow 2).symm) with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h
end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms
