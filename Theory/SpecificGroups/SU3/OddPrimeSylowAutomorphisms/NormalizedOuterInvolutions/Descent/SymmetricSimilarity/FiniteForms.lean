module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Adapted from Atlas/Algebra/FiniteFieldSignSquares.lean,
FiniteFieldBinaryRepresentation.lean and
Atlas/LinearAlgebra/QuadraticBinaryNormalization.lean,
QuadraticDiagonalNormalization.lean, QuadraticDiscriminantClassification.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
See LICENSES/ATLAS-CITATION.cff.
Changes: isolated the discriminant classification needed for ternary similarity,
removed unrelated corollaries, adapted imports and visibility to Lean 4.33.
-/

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Discriminant classification over finite fields of odd characteristic

A nondegenerate binary diagonal form represents one, so a determinant-one
change of basis replaces its coefficients by `1, ab`. Iterating this change
normalizes a diagonal form to ones and its coefficient product. Diagonalization
then proves that the discriminant square class determines every nondegenerate
form of positive dimension.

This is the finite-field input to fixed-field ternary similarity; the only
public export is the actual isometry classification.
-/

noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent.SymmetricSimilarity
variable {F : Type*} [Field F]

private theorem odd_card_mod_two [Finite F] (h2 : (2 : F) ≠ 0) : Nat.card F % 2 = 1 := by
  classical
  let := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  apply FiniteField.odd_card_of_char_ne_two
  intro h
  apply h2
  have hz := CharP.cast_eq_zero F (ringChar F)
  rw [h] at hz
  exact hz

open Polynomial in
/-- The square-value counting argument works over every finite odd field, not just prime fields. -/
private theorem finite_field_binary_represents [Finite F] (h2 : (2 : F) ≠ 0) (a b : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (c : F) : ∃ x y : F, a * x ^ 2 + b * y ^ 2 = c := by
  let := Fintype.ofFinite F
  have hf : degree (C a * X ^ 2 : F[X]) = 2 := degree_C_mul_X_pow 2 ha
  have hg : degree (C b * X ^ 2 - C c : F[X]) = 2 := by
    have hlt : degree (C c : F[X]) < degree (C b * X ^ 2 : F[X]) := by
      rw [degree_C_mul_X_pow 2 hb]
      exact lt_of_le_of_lt degree_C_le (by decide)
    rw [degree_sub_eq_left_of_degree_lt hlt]
    exact degree_C_mul_X_pow 2 hb
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (by simpa only [Nat.card_eq_fintype_card] using odd_card_mod_two h2)
  refine ⟨x, y, ?_⟩
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub] at h
  linear_combination h

/-- The binary quadratic form on an actual product space. -/
private def binaryForm (a b : F) : QuadraticForm F (F × F) :=
  a • (QuadraticMap.sq (R := F)).comp (LinearMap.fst F F F) +
    b • (QuadraticMap.sq (R := F)).comp (LinearMap.snd F F F)

@[simp] private theorem binaryForm_apply (a b : F) (p : F × F) :
    binaryForm a b p = a * p.1 ^ 2 + b * p.2 ^ 2 := by
  simp [binaryForm, QuadraticMap.sq, QuadraticMap.linMulLin_apply, pow_two]

/-- The basis with first vector (x,y), second (-by,ax), has determinant one. -/
private def binaryNormalizationLinear (a b x y : F) (h : a * x ^ 2 + b * y ^ 2 = 1) :
    (F × F) ≃ₗ[F] (F × F) where
  toFun p := (x*p.1-b*y*p.2, y*p.1+a*x*p.2)
  invFun p := (a*x*p.1+b*y*p.2, -y*p.1+x*p.2)
  left_inv p := by
    apply Prod.ext
    · dsimp
      linear_combination p.1 * h
    · dsimp
      linear_combination p.2 * h
  right_inv p := by
    apply Prod.ext
    · dsimp
      linear_combination p.1 * h
    · dsimp
      linear_combination p.2 * h
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' c p := by ext <;> simp [smul_eq_mul] <;> ring

/-- Exact normalization retains the product ab, not just its square class. -/
private def binaryNormalizationIsometry (a b x y : F) (h : a * x ^ 2 + b * y ^ 2 = 1) :
    (binaryForm 1 (a*b)).IsometryEquiv (binaryForm a b) where
  toLinearEquiv := binaryNormalizationLinear a b x y h
  map_app' p := by
    change binaryForm a b (x*p.1-b*y*p.2, y*p.1+a*x*p.2) = binaryForm 1 (a*b) p
    simp only [binaryForm_apply, one_mul]
    linear_combination (p.1 ^ 2 + a*b*p.2 ^ 2) * h

/-- Every nondegenerate diagonal binary form over a finite odd field normalizes to <1,ab>. -/
private theorem finite_binary_normalization [Finite F] (h2 : (2 : F) ≠ 0)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty ((binaryForm a b).IsometryEquiv (binaryForm 1 (a*b))) := by
  obtain ⟨x,y,h⟩ := finite_field_binary_represents h2 a b ha hb 1
  exact ⟨(binaryNormalizationIsometry a b x y h).symm⟩
private abbrev diagonalForm {n : ℕ} (w : Fin n → F) : QuadraticForm F (Fin n → F) :=
  QuadraticMap.weightedSumSquares F w

private def splitFirstTwo (n : ℕ) : (Fin (n + 2) → F) ≃ₗ[F] (F × F) × (Fin n → F) where
  toFun v := ((v 0, v 1), fun i => v i.succ.succ)
  invFun p := Fin.cons p.1.1 (Fin.cons p.1.2 p.2)
  left_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  right_inv p := by rfl
  map_add' v w := rfl
  map_smul' c v := rfl

/-- Splitting off the first two coordinates identifies their actual binary form. -/
private def diagonalSplitTwo {n : ℕ} (a b : F) (w : Fin n → F) :
    (diagonalForm (Fin.cons a (Fin.cons b w))).IsometryEquiv
      ((binaryForm a b).prod (diagonalForm w)) where
  toLinearEquiv := splitFirstTwo n
  map_app' v := by
    simp [QuadraticMap.prod_apply, diagonalForm, QuadraticMap.weightedSumSquares_apply,
      splitFirstTwo, Fin.sum_univ_succ, binaryForm_apply, pow_two, add_assoc]

/-- Any binary isometry acts on the first two coordinates and fixes all others. -/
private def diagonalChangeTwo {n : ℕ} {a b c d : F} (w : Fin n → F)
    (e : (binaryForm a b).IsometryEquiv (binaryForm c d)) :
    (diagonalForm (Fin.cons a (Fin.cons b w))).IsometryEquiv
      (diagonalForm (Fin.cons c (Fin.cons d w))) :=
  (diagonalSplitTwo a b w).trans
    ((e.prod (QuadraticMap.IsometryEquiv.refl (diagonalForm w))).trans
      (diagonalSplitTwo c d w).symm)

/-- Appending a common first coefficient preserves a diagonal isometry. -/
private def diagonalCons {n : ℕ} (a : F) {w z : Fin n → F}
    (e : (diagonalForm w).IsometryEquiv (diagonalForm z)) :
    (diagonalForm (Fin.cons a w)).IsometryEquiv (diagonalForm (Fin.cons a z)) where
  toFun v := Fin.cons (v 0) (e (fun i => v i.succ))
  invFun v := Fin.cons (v 0) (e.symm (fun i => v i.succ))
  left_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  map_add' v t := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change e.toLinearEquiv ((fun i => v i.succ) + (fun i => t i.succ)) j =
        (e.toLinearEquiv (fun i => v i.succ) + e.toLinearEquiv (fun i => t i.succ)) j
      exact congrFun (e.toLinearEquiv.map_add _ _) j
  map_smul' c v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change e.toLinearEquiv (c • (fun i => v i.succ)) j =
        (c • e.toLinearEquiv (fun i => v i.succ)) j
      exact congrFun (e.toLinearEquiv.map_smul c _) j
  map_app' v := by
    have h := e.map_app (fun i => v i.succ)
    simp only [diagonalForm, QuadraticMap.weightedSumSquares_apply,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_eq_mul] at h ⊢
    exact congrArg (fun t => a * (v 0 * v 0) + t) h

/-- Normalized coefficients: all ones followed by the retained final coefficient. -/
private def normalWeights : (n : ℕ) → F → (Fin (n + 1) → F)
  | 0, d => fun _ => d
  | n + 1, d => Fin.cons 1 (normalWeights n d)

/-- Actual diagonal normalization to ones and the exact product of the original coefficients. -/
private theorem finite_diagonal_normalization [Finite F] (h2 : (2 : F) ≠ 0)
    (n : ℕ) (w : Fin (n + 1) → F) (hw : ∀ i, w i ≠ 0) :
    Nonempty ((diagonalForm w).IsometryEquiv
      (diagonalForm (normalWeights n (∏ i, w i)))) := by
  induction n with
  | zero =>
    have he : w = normalWeights 0 (∏ i, w i) := by
      funext i
      fin_cases i
      simp [normalWeights]
    exact ⟨QuadraticForm.weightedSumSquaresCongr he⟩
  | succ n ih =>
    let v : Fin (n + 1) → F := Fin.cons (w 0 * w 1) (fun i => w i.succ.succ)
    have hv : ∀ i, v i ≠ 0 := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact mul_ne_zero (hw 0) (hw 1)
      · exact hw j.succ.succ
    obtain ⟨e⟩ := finite_binary_normalization h2 (w 0) (w 1) (hw 0) (hw 1)
    obtain ⟨f⟩ := ih v hv
    have heq : Fin.cons (w 0) (Fin.cons (w 1) (fun i : Fin n => w i.succ.succ)) = w := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
    have hp : (∏ i, v i) = ∏ i, w i := by
      simp [v, Fin.prod_univ_succ, mul_assoc]
    have e' := (diagonalChangeTwo (fun i : Fin n => w i.succ.succ) e).trans (diagonalCons 1 f)
    rw [heq] at e'
    simpa only [normalWeights, hp] using Nonempty.intro e'

/-- Rescaling only the final coordinate realizes the square-class ambiguity. -/
private def normalWeightsSquareEquiv (n : ℕ) (d e : F) (u : Fˣ)
    (h : e * (u : F) ^ 2 = d) :
    (diagonalForm (normalWeights n d)).IsometryEquiv
      (diagonalForm (normalWeights n e)) := by
  induction n with
  | zero =>
    exact QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
      (fun _ => u) (fun _ => h)
  | succ n ih => exact diagonalCons 1 ih

/-- Diagonal nondegenerate forms of the same positive dimension and square-equivalent
products have an actual isometry. -/
private theorem finite_diagonal_isometry_of_product_square [Finite F] (h2 : (2 : F) ≠ 0)
    (n : ℕ) (w z : Fin (n + 1) → F) (hw : ∀ i, w i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (c : F) (hc : (∏ i, z i) * c ^ 2 = ∏ i, w i) :
    Nonempty ((diagonalForm w).IsometryEquiv (diagonalForm z)) := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0), mul_zero] at hc
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)) hc.symm
  obtain ⟨e⟩ := finite_diagonal_normalization h2 n w hw
  obtain ⟨f⟩ := finite_diagonal_normalization h2 n z hz
  let u := Units.mk0 c hc0
  exact ⟨e.trans ((normalWeightsSquareEquiv n (∏ i, w i) (∏ i, z i) u hc).trans f.symm)⟩

/-- The finite-field discriminant square class suffices for diagonal isometry. -/
private theorem finite_diagonal_isometry_of_square_ratio [Finite F] (h2 : (2 : F) ≠ 0)
    (n : ℕ) (w z : Fin (n + 1) → F) (hw : ∀ i, w i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hs : IsSquare ((∏ i, w i) / ∏ i, z i)) :
    Nonempty ((diagonalForm w).IsometryEquiv (diagonalForm z)) := by
  obtain ⟨c,hc⟩ := hs
  have hz0 : (∏ i, z i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)
  apply finite_diagonal_isometry_of_product_square h2 n w z hw hz c
  rw [← pow_two] at hc
  have h := (div_eq_iff hz0).mp hc
  simpa only [mul_comm] using h.symm

/-- Unit coefficients agree with their underlying field coefficients as actual forms. -/
private theorem weighted_units_eq_diagonal {n : ℕ} (w : Fin n → Fˣ) :
    QuadraticMap.weightedSumSquares F w = diagonalForm (fun i => (w i : F)) := by
  ext v
  simp only [diagonalForm, QuadraticMap.weightedSumSquares_apply, Units.smul_def, smul_eq_mul]

variable [Invertible (2 : F)]

private theorem diagonal_toMatrix {n : ℕ} (w : Fin n → F) :
    (diagonalForm w).toMatrix' = Matrix.diagonal w := by
  ext i j
  simp only [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply,
    QuadraticMap.associated_apply, diagonalForm, QuadraticMap.weightedSumSquares_apply,
    Pi.add_apply, smul_eq_mul]
  by_cases h : i = j
  · subst j
    simp [Pi.single_apply, mul_add, Finset.sum_add_distrib]
    field_simp
    ring
  · simp [h, Ne.symm h, Pi.single_apply, mul_add, Finset.sum_add_distrib]

private theorem diagonal_discr {n : ℕ} (w : Fin n → F) :
    (diagonalForm w).discr' = ∏ i, w i := by
  simp [QuadraticForm.discr', diagonal_toMatrix, Matrix.det_diagonal]

private theorem discr_ratio_isSquare_of_isometry {n : ℕ}
    {Q R : QuadraticForm F (Fin n → F)} (e : Q.IsometryEquiv R)
    (hR : R.discr' ≠ 0) : IsSquare (Q.discr' / R.discr') := by
  have he : R.comp e.toLinearEquiv.toLinearMap = Q := by
    ext v
    exact e.map_app v
  have hd := QuadraticForm.discr'_comp (Q := R) e.toLinearEquiv.toLinearMap
  rw [he] at hd
  refine ⟨(LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det, ?_⟩
  rw [hd, mul_div_cancel_right₀ _ hR]

private theorem associated_separating_of_polar_nondegenerate {V : Type*}
    [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) : Q.associated.SeparatingLeft := by
  intro x hx
  apply hQ.1
  intro y
  have hp := congrArg (fun B => B x y) (QuadraticMap.two_nsmul_associated (S := F) Q)
  simp only [LinearMap.smul_apply, nsmul_eq_mul, hx, mul_zero] at hp
  exact hp.symm

private theorem discr_ne_zero_of_nondegenerate {n : ℕ} (Q : QuadraticForm F (Fin n → F))
    (hQ : Q.polarBilin.Nondegenerate) : Q.discr' ≠ 0 := by
  have ha := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (associated_separating_of_polar_nondegenerate Q hQ)
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Pi.basisFun F (Fin n))).mp ha

private theorem finite_nondegenerate_diagonalization {n : ℕ}
    (Q : QuadraticForm F (Fin n → F)) (hQ : Q.polarBilin.Nondegenerate) :
    ∃ w : Fin n → F, (∀ i, w i ≠ 0) ∧ Nonempty (Q.IsometryEquiv (diagonalForm w)) := by
  have h : ∃ w : Fin n → Fˣ, Nonempty (Q.IsometryEquiv
      (QuadraticMap.weightedSumSquares F w)) := by
    have hh := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
      (associated_separating_of_polar_nondegenerate Q hQ)
    rw [Module.finrank_fin_fun] at hh
    exact hh
  obtain ⟨w, he⟩ := h
  refine ⟨fun i => (w i : F), fun i => (w i).ne_zero, ?_⟩
  simpa only [weighted_units_eq_diagonal] using he

public theorem finite_nondegenerate_isometry_iff_discr_square [Finite F]
    (h2 : (2 : F) ≠ 0) (n : ℕ)
    (Q R : QuadraticForm F (Fin (n + 1) → F))
    (hQ : Q.polarBilin.Nondegenerate) (hR : R.polarBilin.Nondegenerate) :
    Nonempty (Q.IsometryEquiv R) ↔ IsSquare (Q.discr' / R.discr') := by
  have hQ0 := discr_ne_zero_of_nondegenerate Q hQ
  have hR0 := discr_ne_zero_of_nondegenerate R hR
  constructor
  · rintro ⟨e⟩
    exact discr_ratio_isSquare_of_isometry e hR0
  · intro hs
    obtain ⟨w, hw, ⟨e⟩⟩ := finite_nondegenerate_diagonalization Q hQ
    obtain ⟨z, hz, ⟨f⟩⟩ := finite_nondegenerate_diagonalization R hR
    have hw0 : (∏ i, w i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
    have hz0 : (∏ i, z i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)
    have he : IsSquare ((∏ i, w i) / Q.discr') := by
      simpa only [diagonal_discr] using discr_ratio_isSquare_of_isometry e.symm hQ0
    have hf : IsSquare (R.discr' / ∏ i, z i) := by
      simpa only [diagonal_discr] using discr_ratio_isSquare_of_isometry f
        (show (diagonalForm z).discr' ≠ 0 by rwa [diagonal_discr])
    have heq : ((∏ i, w i) / Q.discr') * (Q.discr' / R.discr') *
        (R.discr' / ∏ i, z i) = (∏ i, w i) / ∏ i, z i := by
      field_simp
    have h := (he.mul hs).mul hf
    rw [heq] at h
    obtain ⟨g⟩ := finite_diagonal_isometry_of_square_ratio h2 n w z hw hz h
    exact ⟨e.trans (g.trans f.symm)⟩

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent.SymmetricSimilarity
