module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Contracts
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.InverseRows
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Packed
import Mathlib.Tactic.FinCases

/-!
# Row certificates for the thirteen sourced matrix relations

The computational statements concern only literal packed rows. Their soundness
identifies left-to-right row evaluation with ordinary matrix multiplication,
and equality on every coordinate row gives the complete matrix identity.
Saved traces permit checking each intermediate row without repeatedly reducing
a nested word. The final lemma constructs the two units required by
`MatrixRelations`; over this finite matrix ring a right inverse is also a left
inverse. None of the finite identity hypotheses is asserted here.

Source: the unchanged ATLAS HSG1-P1.M, transcribed in Descent.Words. The signed
alphabet is a, b, inverse a, inverse b. The candidate inverse table is defined
separately and must be verified. This module imports Contracts rather than the
Descent assembly, so the certificate and assembly remain acyclic.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate
open Sporadic.LeechRelated.HS
open Thompson.BinaryMatrix

/-- Candidate inverse; invertibility is a separate finite identity. -/
def inverseMatrix : Mat := decode 1408 inverseRows

def letterRows : Fin 4 → Array Nat := ![aRows, bRows, aRows, inverseRows]

def letterMatrix (i : Fin 4) : Mat := decode 1408 (letterRows i)

/-- The exact signed source word, with the supplied candidate inverse entries. -/
def matrixWord (i : Fin 13) : Mat :=
  ((AtlasPresentation.relatorLetters i).map letterMatrix).prod

theorem letterRows_size (i : Fin 4) : (letterRows i).size = 1408 := by
  fin_cases i
  · exact Density.aRows_size
  · exact Density.bRows_size
  · exact Density.aRows_size
  · decide +kernel

/-- Run a source word on a packed row, in ordinary multiplication order. -/
def run (x : Nat) : List (Fin 4) → Nat
  | [] => x
  | c :: cs => run (PackedBinaryRows.listProduct x 0 (letterRows c).toList) cs

theorem run_sound (cs : List (Fin 4)) (x : Nat) :
    Density.vectorOfBits (run x cs) =
      Matrix.vecMul (Density.vectorOfBits x) ((cs.map letterMatrix).prod) := by
  induction cs generalizing x with
  | nil => simp [run]
  | cons c cs ih =>
    rw [run, ih, List.map_cons, List.prod_cons, ← Matrix.vecMul_vecMul]
    exact congrArg (fun v => Matrix.vecMul v ((cs.map letterMatrix).prod))
      (PackedBinaryRows.vecMul_decode_of_listProduct 1408 (letterRows c) x
        (PackedBinaryRows.listProduct x 0 (letterRows c).toList) (letterRows_size c) rfl).symm

theorem vecMul_basis (M : Mat) (i : Fin 1408) :
    Matrix.vecMul (Density.vectorOfBits (2 ^ i.val)) M = M i := by
  funext j
  simp [Matrix.vecMul, dotProduct, Density.vectorOfBits, bit, Nat.testBit_two_pow,
    ← Fin.ext_iff]

/-- Equality on every coordinate row certifies the complete matrix word. -/
theorem matrixWord_eq_one_of_run (i : Fin 13)
    (h : ∀ j : Fin 1408, run (2 ^ j.val) (AtlasPresentation.relatorLetters i) = 2 ^ j.val) :
    matrixWord i = 1 := by
  ext j k
  have hx := run_sound (AtlasPresentation.relatorLetters i) (2 ^ j.val)
  rw [h j, vecMul_basis] at hx
  have he := congrFun hx k
  simpa [matrixWord, Density.vectorOfBits, bit, Nat.testBit_two_pow,
    Matrix.one_apply, Fin.ext_iff] using he.symm

/-- A trace checks each saved intermediate row separately, avoiding repeated
normalization of a long nested matrix word. The empty trace is rejected. -/
def checkTrace : List (Fin 4) → List Nat → Bool
  | [], [_] => true
  | c :: cs, x :: y :: ys =>
      (PackedBinaryRows.listProduct x 0 (letterRows c).toList == y) &&
        checkTrace cs (y :: ys)
  | _, _ => false

theorem checkTrace_sound (cs : List (Fin 4)) (x : Nat) (xs : List Nat)
    (h : checkTrace cs (x :: xs) = true) : run x cs = (x :: xs).getLast! := by
  induction cs generalizing x xs with
  | nil => cases xs <;> simp_all [checkTrace, run]
  | cons c cs ih =>
    cases xs with
    | nil => simp [checkTrace] at h
    | cons y ys =>
      simp only [checkTrace, Bool.and_eq_true, beq_iff_eq] at h
      rw [run, h.1, ih y ys h.2]
      simp

/-- Saved row traces are a sufficient, kernel-checkable certificate for one
literal source relation. Every basis row and both endpoints are retained. -/
theorem matrixWord_eq_one_of_traces (i : Fin 13)
    (h : ∀ j : Fin 1408, ∃ xs : List Nat,
      checkTrace (AtlasPresentation.relatorLetters i) (2 ^ j.val :: xs) = true ∧
        (2 ^ j.val :: xs).getLast! = 2 ^ j.val) : matrixWord i = 1 := by
  apply matrixWord_eq_one_of_run
  intro j
  obtain ⟨xs, hc, he⟩ := h j
  exact (checkTrace_sound _ _ xs hc).trans he

/-- Concrete inverse identities and coordinate checks supply exactly the units
and all thirteen words required by the marked-presentation consumer. -/
theorem matrixRelations_of_identities
    (hb : matrixB * inverseMatrix = 1)
    (hw : ∀ i : Fin 13, matrixWord i = 1) : MatrixRelations := by
  have ha := hw 0
  change matrixA * (matrixA * 1) = 1 at ha
  rw [mul_one] at ha
  let a : Matˣ := ⟨matrixA, matrixA, ha, ha⟩
  let b : Matˣ := ⟨matrixB, inverseMatrix, hb, mul_eq_one_comm.mp hb⟩
  refine ⟨a, b, rfl, rfl, fun i => Units.ext ?_⟩
  have hl (j : Fin 4) : (Units.coeHom Mat) (AtlasPresentation.letter a b j) =
      letterMatrix j := by
    fin_cases j <;> rfl
  have hword : (Units.coeHom Mat) (AtlasPresentation.word a b i) = matrixWord i := by
    simp only [AtlasPresentation.word, map_list_prod, List.map_map, Function.comp_def, hl, matrixWord]
  exact hword.trans (hw i)

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate
