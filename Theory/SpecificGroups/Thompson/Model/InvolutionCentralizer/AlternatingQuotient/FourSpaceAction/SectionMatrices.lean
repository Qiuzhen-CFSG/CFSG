module

public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.ActionData
public import Mathlib.LinearAlgebra.Matrix.ToLin
/-!
# The literal 29/21 matrix section for Thompson max3

The rectangular packed-row checker proves the right inverse of the section
basis and its equivariance under the two max3 matrices. The coordinate
projection onto the last eight entries kills the first twenty-one rows and
intertwines the section matrices with the published factor matrices.

These are checked linear-algebra witnesses for the four-space action used in
GLS3 Table 5.3x and Aschbacher--Smith A.2.19. Data provenance is retained in
`AlternatingQuotient/source/README.md`.
-/

public section
open scoped BigOperators Matrix
namespace Thompson.InvolutionCentralizer.AlternatingQuotient
open BinaryMatrix

theorem decodeRows_mul {m n p : ℕ} (a b c : Array ℕ)
    (h : ∀ i : Fin m, rowProduct a[i.val]! b n = c[i.val]!) :
    decodeRows m n a * decodeRows n p b = decodeRows m p c := by
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = bit c[i.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun k => bit a[i.val]! k * bit b[k]! j.val),
    ← bit_rowProduct, h i]

theorem decodeRows_mul_eq {m n p q : ℕ} (a b c d : Array ℕ)
    (h : ∀ i : Fin m, rowProduct a[i.val]! b n = rowProduct c[i.val]! d q) :
    decodeRows m n a * decodeRows n p b = decodeRows m q c * decodeRows q p d := by
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) =
    ∑ k : Fin q, bit c[i.val]! k.val * bit d[k.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun k => bit a[i.val]! k * bit b[k]! j.val),
    Fin.sum_univ_eq_sum_range (fun k => bit c[i.val]! k * bit d[k]! j.val),
    ← bit_rowProduct, ← bit_rowProduct, h i]

theorem decodeRows_mul_one {m n : ℕ} (a b : Array ℕ)
    (h : ∀ i : Fin m, rowProduct a[i.val]! b n = 2 ^ i.val) :
    decodeRows m n a * decodeRows n m b = 1 := by
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => bit a[i.val]! k * bit b[k]! j.val),
    ← bit_rowProduct, h i]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

set_option maxRecDepth 2048 in
private theorem rightInverse_check :
    (List.finRange 29).all (fun i => decide
      (rowProduct sectionBasisRows[i.val]! sectionRightInverseRows 248 = 2 ^ i.val)) = true := by
  decide +kernel

theorem sectionBasis_mul_rightInverse : sectionBasisMatrix * sectionRightInverseMatrix = 1 := by
  apply decodeRows_mul_one
  have h := rightInverse_check
  simpa only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] using h

set_option maxRecDepth 2048 in
private theorem sectionA_check :
    (List.finRange 29).all (fun i => decide
      (rowProduct sectionBasisRows[i.val]! wordARows 248 =
       rowProduct sectionARows[i.val]! sectionBasisRows 29)) = true := by
  decide +kernel

theorem sectionBasis_mul_wordA : sectionBasisMatrix * wordAMatrix = sectionAMatrix * sectionBasisMatrix := by
  apply decodeRows_mul_eq
  have h := sectionA_check
  simpa only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] using h

set_option maxRecDepth 2048 in
private theorem sectionB_check :
    (List.finRange 29).all (fun i => decide
      (rowProduct sectionBasisRows[i.val]! wordBRows 248 =
       rowProduct sectionBRows[i.val]! sectionBasisRows 29)) = true := by
  decide +kernel

theorem sectionBasis_mul_wordB : sectionBasisMatrix * wordBMatrix = sectionBMatrix * sectionBasisMatrix := by
  apply decodeRows_mul_eq
  have h := sectionB_check
  simpa only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] using h


/-- Projection from section coordinates to the eight quotient coordinates. -/
@[expose] def factorProjectionRows : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 64, 128]

@[expose] def factorProjection : Matrix (Fin 29) (Fin 8) (ZMod 2) :=
  decodeRows 29 8 factorProjectionRows

/-- The chosen lift of quotient coordinates into section coordinates. -/
@[expose] def factorLiftRows : Array ℕ := #[2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456]

@[expose] def factorLift : Matrix (Fin 8) (Fin 29) (ZMod 2) :=
  decodeRows 8 29 factorLiftRows

theorem factorLift_mul_projection : factorLift * factorProjection = 1 := by
  apply decodeRows_mul_one
  decide +kernel

theorem sectionA_mul_projection : sectionAMatrix * factorProjection =
    factorProjection * factorAMatrix := by
  apply decodeRows_mul_eq
  decide +kernel

theorem sectionB_mul_projection : sectionBMatrix * factorProjection =
    factorProjection * factorBMatrix := by
  apply decodeRows_mul_eq
  decide +kernel

/-- Coordinate form of the projection: precisely the final eight entries survive. -/
theorem factorProjection_apply (i : Fin 29) (j : Fin 8) :
    factorProjection i j = if i.val = 21 + j.val then 1 else 0 := by
  have h : (List.finRange 29).all (fun i => (List.finRange 8).all (fun j =>
      decide (factorProjection i j = if i.val = 21 + j.val then 1 else 0))) = true := by
    decide +kernel
  have := (show ∀ i : Fin 29, ∀ j : Fin 8,
      factorProjection i j = if i.val = 21 + j.val then 1 else 0 from by
    simpa only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] using h)
  exact this i j

/-- The factor is the literal bottom-right block, with zero above it. -/
theorem sectionA_factor_entries :
    (∀ i : Fin 21, ∀ j : Fin 8, sectionAMatrix (i.castAdd 8) (j.natAdd 21) = 0) ∧
    (∀ i j : Fin 8, sectionAMatrix (i.natAdd 21) (j.natAdd 21) = factorAMatrix i j) := by
  have h₁ : (List.finRange 21).all (fun i => (List.finRange 8).all (fun j =>
      decide (sectionAMatrix (i.castAdd 8) (j.natAdd 21) = 0))) = true := by
    decide +kernel
  have h₂ : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      decide (sectionAMatrix (i.natAdd 21) (j.natAdd 21) = factorAMatrix i j))) = true := by
    decide +kernel
  simpa only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] using And.intro h₁ h₂

theorem sectionB_factor_entries :
    (∀ i : Fin 21, ∀ j : Fin 8, sectionBMatrix (i.castAdd 8) (j.natAdd 21) = 0) ∧
    (∀ i j : Fin 8, sectionBMatrix (i.natAdd 21) (j.natAdd 21) = factorBMatrix i j) := by
  have h₁ : (List.finRange 21).all (fun i => (List.finRange 8).all (fun j =>
      decide (sectionBMatrix (i.castAdd 8) (j.natAdd 21) = 0))) = true := by
    decide +kernel
  have h₂ : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      decide (sectionBMatrix (i.natAdd 21) (j.natAdd 21) = factorBMatrix i j))) = true := by
    decide +kernel
  simpa only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] using And.intro h₁ h₂

end Thompson.InvolutionCentralizer.AlternatingQuotient
