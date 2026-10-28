module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic
/-!
# Sparse integral calculation for the two F₄ end roots

Sparse lists are interpreted as sums of matrix units. Proving multiplication
and trace for that interpretation permits kernel reduction of the nine integral
trace coefficients. The operator tables are connected to the actual Geck
operators in `Operators.lean`; the tables alone assert no model identification.

Source: Geck's integral simple-root operators, as defined in
`IntegralGeckConstruction.lean`; GLS3, §1.12 and Table 2.4, type VI.
-/

@[expose] public section
namespace ReeF4.Cartan.FieldSeparation.TraceValues
abbrev Entry := Fin 52 × Fin 52 × ℤ
abbrev Sparse := List Entry

def matrix (a : Sparse) : Matrix (Fin 52) (Fin 52) ℤ :=
  (a.map fun e => Matrix.single e.1 e.2.1 e.2.2).sum

def sparseMul (a b : Sparse) : Sparse :=
  a.flatMap fun e => b.filterMap fun f =>
    if e.2.1 = f.1 then some (e.1, f.2.1, e.2.2 * f.2.2) else none

def sparseTrace (a : Sparse) : ℤ :=
  (a.map fun e => if e.1 = e.2.1 then e.2.2 else 0).sum

@[simp] lemma matrix_nil : matrix [] = 0 := rfl

@[simp] lemma matrix_cons (e : Entry) (a : Sparse) :
    matrix (e :: a) = Matrix.single e.1 e.2.1 e.2.2 + matrix a := rfl

lemma matrix_append (a b : Sparse) : matrix (a ++ b) = matrix a + matrix b := by
  simp [matrix]

lemma matrix_mul (a b : Sparse) : matrix (sparseMul a b) = matrix a * matrix b := by
  have step (e : Entry) :
      matrix (b.filterMap fun f => if e.2.1 = f.1 then
        some (e.1, f.2.1, e.2.2 * f.2.2) else none) =
      Matrix.single e.1 e.2.1 e.2.2 * matrix b := by
    induction b with
    | nil => simp [matrix]
    | cons f b ih =>
      by_cases h : e.2.1 = f.1
      · simp only [List.filterMap_cons, if_pos h, matrix_cons, Matrix.mul_add]
        rw [show Matrix.single e.1 e.2.1 e.2.2 * Matrix.single f.1 f.2.1 f.2.2 =
          Matrix.single e.1 f.2.1 (e.2.2 * f.2.2) by
            rw [h, Matrix.single_mul_single_same]]
        rw [ih]
      · simp only [List.filterMap_cons, if_neg h, matrix_cons, Matrix.mul_add]
        rw [Matrix.single_mul_single_of_ne e.2.2 _ _ _ h, zero_add]
        exact ih
  induction a with
  | nil => simp [sparseMul, matrix]
  | cons e a ih =>
    change matrix ((_ ++ sparseMul a b)) = matrix (e :: a) * matrix b
    rw [matrix_append, step, ih, matrix_cons, Matrix.add_mul]

lemma trace_matrix (a : Sparse) : Matrix.trace (matrix a) = sparseTrace a := by
  induction a with
  | nil => simp [matrix, sparseTrace]
  | cons e a ih =>
    by_cases h : e.1 = e.2.1
    · simpa [matrix, sparseTrace, h] using ih
    · simpa [matrix, sparseTrace, h, Matrix.trace_single_eq_of_ne _ _ _ h] using ih
def identityEntries : Sparse :=
  [(0, 0, 1), (1, 1, 1), (2, 2, 1), (3, 3, 1), (4, 4, 1),
    (5, 5, 1), (6, 6, 1), (7, 7, 1), (8, 8, 1), (9, 9, 1),
    (10, 10, 1), (11, 11, 1), (12, 12, 1), (13, 13, 1), (14, 14, 1),
    (15, 15, 1), (16, 16, 1), (17, 17, 1), (18, 18, 1), (19, 19, 1),
    (20, 20, 1), (21, 21, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1),
    (25, 25, 1), (26, 26, 1), (27, 27, 1), (28, 28, 1), (29, 29, 1),
    (30, 30, 1), (31, 31, 1), (32, 32, 1), (33, 33, 1), (34, 34, 1),
    (35, 35, 1), (36, 36, 1), (37, 37, 1), (38, 38, 1), (39, 39, 1),
    (40, 40, 1), (41, 41, 1), (42, 42, 1), (43, 43, 1), (44, 44, 1),
    (45, 45, 1), (46, 46, 1), (47, 47, 1), (48, 48, 1), (49, 49, 1),
    (50, 50, 1), (51, 51, 1)]

def positive0Linear : Sparse :=
  [(0, 25, 1), (7, 9, 1), (8, 6, 1), (13, 17, 1), (15, 19, 1),
    (16, 12, 1), (18, 14, 1), (26, 0, 2), (26, 1, 1), (30, 34, 1),
    (31, 35, 1), (32, 28, 1), (33, 29, 1), (40, 38, 1), (41, 39, 1),
    (48, 46, 1), (49, 47, 1)]

def positive0Quadratic : Sparse :=
  [(26, 25, 1)]

def negative0Linear : Sparse :=
  [(0, 26, 1), (6, 8, 1), (9, 7, 1), (12, 16, 1), (14, 18, 1),
    (17, 13, 1), (19, 15, 1), (25, 0, 2), (25, 1, 1), (28, 32, 1),
    (29, 33, 1), (34, 30, 1), (35, 31, 1), (38, 40, 1), (39, 41, 1),
    (46, 48, 1), (47, 49, 1)]

def negative0Quadratic : Sparse :=
  [(25, 26, 1)]

def positive3Linear : Sparse :=
  [(3, 43, 1), (5, 51, 1), (6, 39, 1), (8, 41, 1), (10, 42, 1),
    (14, 47, 2), (18, 49, 2), (22, 50, 2), (24, 37, 2), (28, 38, 2),
    (32, 40, 2), (36, 4, 1), (37, 21, 1), (38, 17, 1), (40, 13, 1),
    (44, 2, 1), (44, 3, 2), (45, 11, 1), (46, 9, 1), (47, 35, 1),
    (48, 7, 1), (49, 31, 1), (50, 27, 1)]

def positive3Quadratic : Sparse :=
  [(14, 35, 1), (18, 31, 1), (22, 27, 1), (24, 21, 1), (28, 17, 1),
    (32, 13, 1), (44, 43, 1)]

def negative3Linear : Sparse :=
  [(3, 44, 1), (4, 36, 1), (7, 48, 1), (9, 46, 1), (11, 45, 1),
    (13, 40, 2), (17, 38, 2), (21, 37, 2), (27, 50, 2), (31, 49, 2),
    (35, 47, 2), (37, 24, 1), (38, 28, 1), (39, 6, 1), (40, 32, 1),
    (41, 8, 1), (42, 10, 1), (43, 2, 1), (43, 3, 2), (47, 14, 1),
    (49, 18, 1), (50, 22, 1), (51, 5, 1)]

def negative3Quadratic : Sparse :=
  [(13, 32, 1), (17, 28, 1), (21, 24, 1), (27, 22, 1), (31, 18, 1),
    (35, 14, 1), (43, 44, 1)]

def positive0Entries : Fin 3 → Sparse
  | ⟨0, _⟩ => identityEntries
  | ⟨1, _⟩ => positive0Linear
  | _ => positive0Quadratic

def negative0Entries : Sparse :=
  identityEntries ++ negative0Linear ++ negative0Quadratic

def positive3Entries : Fin 3 → Sparse
  | ⟨0, _⟩ => identityEntries
  | ⟨1, _⟩ => positive3Linear
  | _ => positive3Quadratic

def negative3Entries : Sparse :=
  identityEntries ++ negative3Linear ++ negative3Quadratic

def coefficients : Fin 3 → Fin 3 → ℤ := !![52, 36, 7; 18, 10, 2; 1, 0, 0]

set_option maxRecDepth 4000 in
lemma coefficient_check (a b : Fin 3) :
    sparseTrace (sparseMul (sparseMul (positive0Entries a) (positive3Entries b))
      (sparseMul negative0Entries negative3Entries)) = coefficients a b := by
  fin_cases a <;> fin_cases b <;> decide +kernel

variable {S : Type*} [CommRing S]

def scalarMatrix (a : Sparse) : Matrix (Fin 52) (Fin 52) S :=
  (matrix a).map (Int.castRingHom S)

def positive0 (t : S) : Matrix (Fin 52) (Fin 52) S :=
  ∑ a : Fin 3, t ^ a.val • scalarMatrix (positive0Entries a)

def positive3 (u : S) : Matrix (Fin 52) (Fin 52) S :=
  ∑ b : Fin 3, u ^ b.val • scalarMatrix (positive3Entries b)

def negative0 : Matrix (Fin 52) (Fin 52) S := scalarMatrix negative0Entries

def negative3 : Matrix (Fin 52) (Fin 52) S := scalarMatrix negative3Entries

lemma scalarMatrix_mul (a b : Sparse) :
    scalarMatrix (S := S) (sparseMul a b) = scalarMatrix a * scalarMatrix b := by
  simp only [scalarMatrix, matrix_mul, Matrix.map_mul]

lemma trace_coefficients (a b : Fin 3) :
    Matrix.trace (scalarMatrix (S := S) (positive0Entries a) *
      scalarMatrix (positive3Entries b) * (negative0 * negative3)) =
      (coefficients a b : S) := by
  change Matrix.trace (scalarMatrix (positive0Entries a) *
    scalarMatrix (positive3Entries b) *
    (scalarMatrix negative0Entries * scalarMatrix negative3Entries)) = _
  rw [← scalarMatrix_mul, ← scalarMatrix_mul, ← scalarMatrix_mul]
  rw [scalarMatrix, ← AddMonoidHom.map_trace, trace_matrix, coefficient_check]
  rfl

lemma finite_trace (t u : S) :
    Matrix.trace (positive0 t * positive3 u * (negative0 * negative3)) =
      52 + 18 * t + 36 * u + t ^ 2 + 7 * u ^ 2 + 10 * t * u + 2 * t * u ^ 2 := by
  simp only [positive0, positive3, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    trace_coefficients, smul_eq_mul]
  simp [Fin.sum_univ_succ, coefficients]
  ring

end ReeF4.Cartan.FieldSeparation.TraceValues
