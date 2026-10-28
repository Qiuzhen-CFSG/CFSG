module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.PackedGenerators
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PositiveWords

/-!
# Streaming certificates for the three HS commutator words

This row multiplier consumes the two coefficient planes from their low bits,
shifting once per matrix row. Its equality with `Packed.rowProduct` is proved
before any numerical certificate is used. Saved intermediate rows can then be
checked separately, and equality on all coordinate rows proves the matrix word.

The three positive words are exactly indices 4--6 of the retained HSG1-P1.M,
after the inverse substitutions proved in `PositiveWords`. The application
lemmas below still require all numerical row checks. They are not assertions
that a source relation has been verified. Source and benchmark details are in
`source/README.md`; the unchanged matrices are in `TracePair/source/`.
-/

@[expose] public section
open Representation.HigmanSims.LargeModels.TracePair.Certificates
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Streaming
open Packed

def product : Row → Mat → Row
  | _, [] => (0, 0)
  | (a, b), r :: rs => Base.addRow
      (Base.addRow (if a % 2 = 1 then r else (0, 0))
        (if b % 2 = 1 then Base.timesT r else (0, 0)))
      (product (a / 2, b / 2) rs)

private theorem lowBit (a k : ℕ) :
    (decide ((a >>> k) % 2 = 1)) = a.testBit k := by
  rw [← Nat.testBit_zero]
  simp only [Nat.testBit_shiftRight, Nat.add_zero]

theorem product_shift (a : Row) (b : Mat) (k : ℕ) :
    product (a.1 >>> k, a.2 >>> k) b = rowProductFrom a b k := by
  induction b generalizing k with
  | nil => rfl
  | cons b bs ih =>
    rw [product, rowProductFrom, ← ih (k + 1)]
    simp only [Nat.shiftRight_succ]
    congr 2 <;> simp only [← lowBit, decide_eq_true_eq]

theorem product_eq (a : Row) (b : Mat) : product a b = Packed.rowProduct a b := by
  simpa only [Nat.shiftRight_zero, Prod.eta, Packed.rowProduct] using product_shift a b 0

/-- Streamed row arithmetic gives ordinary matrix multiplication over Four. -/
theorem eval_product (n : ℕ) (a b c : Mat) (hb : b.length = n)
    (h : ∀ i : Fin n, product (a.getD i.val (0, 0)) b = c.getD i.val (0, 0)) :
    Packed.eval n a * Packed.eval n b = Packed.eval n c := by
  apply Packed.eval_product n a b c hb
  intro i
  rw [← product_eq]
  exact h i

theorem eval_inverse (n : ℕ) (a b : Mat) (hb : b.length = n)
    (h : ∀ i : Fin n, product (a.getD i.val (0, 0)) b = (2 ^ i.val, 0)) :
    Packed.eval n a * Packed.eval n b = 1 := by
  apply Packed.eval_inverse n a b hb
  intro i
  rw [← product_eq]
  exact h i

/-- A packed row, interpreted in the literal degree-896 space. -/
def vector (a : Row) : Fin 896 → Four := fun i => Packed.decode a i.val

def letterRows (c : Bool) : Mat := if c then generatorRowsB else generatorRowsA

def letterMatrix (c : Bool) := Packed.eval 896 (letterRows c)

theorem letterRows_length (c : Bool) : (letterRows c).length = 896 := by
  cases c
  · exact generatorRowsA_length
  · exact generatorRowsB_length

/-- Read the positive source letters in the original multiplication order. -/
def run (a : Row) : List Bool → Row
  | [] => a
  | c :: cs => run (product a (letterRows c)) cs

theorem vector_product (a : Row) (b : Mat) (hb : b.length = 896) :
    vector (product a b) = Matrix.vecMul (vector a) (Packed.eval 896 b) := by
  funext i
  exact (congrArg (fun r => Packed.decode r i.val) (product_eq a b)).trans
    (Packed.decode_rowProduct a b 896 hb i.val)

theorem run_sound (a : Row) (cs : List Bool) :
    vector (run a cs) = Matrix.vecMul (vector a) ((cs.map letterMatrix).prod) := by
  induction cs generalizing a with
  | nil => simp [run]
  | cons c cs ih =>
    rw [run, ih, List.map_cons, List.prod_cons, ← Matrix.vecMul_vecMul]
    exact congrArg (fun v => Matrix.vecMul v ((cs.map letterMatrix).prod))
      (vector_product a (letterRows c) (letterRows_length c))

theorem vecMul_basis (M : Matrix (Fin 896) (Fin 896) Four) (i : Fin 896) :
    Matrix.vecMul (vector (2 ^ i.val, 0)) M = M i := by
  funext j
  simp [Matrix.vecMul, dotProduct, vector, Packed.decode, Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    Nat.testBit_two_pow, ← Fin.ext_iff]

/-- A checked coordinate orbit gives that literal row of the matrix word. -/
theorem word_row_eq_of_run (cs : List Bool) (i : Fin 896)
    (h : run (2 ^ i.val, 0) cs = (2 ^ i.val, 0)) :
    (cs.map letterMatrix).prod i = (1 : Matrix (Fin 896) (Fin 896) Four) i := by
  have hi := run_sound (2 ^ i.val, 0) cs
  rw [h, vecMul_basis] at hi
  exact hi.symm.trans (by simpa using vecMul_basis (1 : Matrix (Fin 896) (Fin 896) Four) i)

/-- Checking every coordinate row proves a full matrix word identity. -/
theorem word_eq_one_of_runs (cs : List Bool)
    (h : ∀ i : Fin 896, run (2 ^ i.val, 0) cs = (2 ^ i.val, 0)) :
    (cs.map letterMatrix).prod = 1 := by
  funext i
  exact word_row_eq_of_run cs i (h i)

/-- Each saved intermediate row is checked independently. -/
def checkTrace : List Bool → List Row → Bool
  | [], [_] => true
  | c :: cs, a :: b :: bs => (product a (letterRows c) == b) && checkTrace cs (b :: bs)
  | _, _ => false

theorem checkTrace_sound (cs : List Bool) (a : Row) (as : List Row)
    (h : checkTrace cs (a :: as) = true) : run a cs = (a :: as).getLast! := by
  induction cs generalizing a as with
  | nil => cases as <;> simp_all [checkTrace, run]
  | cons c cs ih =>
    cases as with
    | nil => simp [checkTrace] at h
    | cons b bs =>
      simp only [checkTrace, Bool.and_eq_true, beq_iff_eq] at h
      rw [run, h.1, ih b bs h.2]
      simp

def word4 : List Bool := (List.replicate 5
  [false, true, true, true, true, false, true]).flatten

def word5 : List Bool := (List.replicate 3
  [false, true, true, true, true, false, true, true, true, true, false, true, false, true]).flatten

def word6 : List Bool := (List.replicate 6
  [false, true, true, true, false, true, true]).flatten

theorem word4_semantics : (word4.map letterMatrix).prod = positiveRelation
    (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 4 := by
  simp [word4, letterMatrix, letterRows,
    positiveRelation, pow_succ, mul_assoc]

theorem word5_semantics : (word5.map letterMatrix).prod = positiveRelation
    (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 5 := by
  simp [word5, letterMatrix, letterRows,
    positiveRelation, pow_succ, mul_assoc]

theorem word6_semantics : (word6.map letterMatrix).prod = positiveRelation
    (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 6 := by
  simp [word6, letterMatrix, letterRows,
    positiveRelation, pow_succ, mul_assoc]

theorem commutator_five_of_runs
    (h : ∀ i : Fin 896, run (2 ^ i.val, 0) word4 = (2 ^ i.val, 0)) :
    positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 4 = 1 :=
  word4_semantics.symm.trans (word_eq_one_of_runs word4 h)

theorem nested_commutator_three_of_runs
    (h : ∀ i : Fin 896, run (2 ^ i.val, 0) word5 = (2 ^ i.val, 0)) :
    positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 5 = 1 :=
  word5_semantics.symm.trans (word_eq_one_of_runs word5 h)

theorem square_commutator_six_of_runs
    (h : ∀ i : Fin 896, run (2 ^ i.val, 0) word6 = (2 ^ i.val, 0)) :
    positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 6 = 1 :=
  word6_semantics.symm.trans (word_eq_one_of_runs word6 h)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Streaming
