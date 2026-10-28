module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Simple.Models
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.Tactic.LinearCombination

/-!
# Soundness of packed F₄ extension equations

A pair of natural numbers records the real and omega coefficients of a
linear form in the 81 unknown matrix entries. XOR adds linear forms;
interchanging the two masks and adding one mask implements multiplication
by omega. We prove these operations agree with evaluation over F₄.

Each intertwining equation is assembled from eighteen single-coordinate
forms. Thus finite checks compare packed integers, without repeatedly
normalizing long sums of field-valued matrices. A checked row combination
for each coordinate of a column forces a zero column, contradicting X²=1.

Source context: the elementary extension obstruction for Guralnick–Malle I,
Proposition 5.1, pp.15–16. Packed-bit addition uses the existing Thompson
certificate lemma; no native computation or unproved matrix identities enter.
-/

@[expose] public noncomputable section
open Matrix
open scoped BigOperators
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine.Simple.Certificate
open Representation.SL3FourNaturalDual
abbrev EquationIndex := Fin 2 × Fin 9 × Fin 9
def evaluate (X A : Matrix9) : F := ∑ r, ∑ c, A r c * X r c
lemma evaluate_add (X A B : Matrix9) :
    evaluate X (A + B) = evaluate X A + evaluate X B := by
  simp [evaluate, add_mul, Finset.sum_add_distrib]
lemma evaluate_smul (X A : Matrix9) (a : F) :
    evaluate X (a • A) = a * evaluate X A := by
  simp [evaluate, mul_assoc, Finset.mul_sum]
def unitRow (r c : Fin 9) : Matrix9 := fun i j => if i = r ∧ j = c then 1 else 0
lemma evaluate_single (X : Matrix9) (r c : Fin 9) :
    evaluate X (unitRow r c) = X r c := by
  simp [evaluate, unitRow, ite_and]
def sourceIndex : Fin 2 → Fin 4 := ![0, 1]
def targetIndex : Fin 2 → Fin 4 := ![2, 3]
lemma zero_column_contradiction (X : Matrix9) (h : X * X = 1)
    (hc : ∀ r, X r 0 = 0) : False := by
  have he := congrArg (fun A : Matrix9 => A 0 0) h
  simp [Matrix.mul_apply, hc] at he
open Thompson.BinaryMatrix
/-- Packed real and omega coefficients of a linear form in the 81 entries. -/
abbrev Row := Nat × Nat
def decode (a : Row) (i : Nat) : F :=
  algebraMap (ZMod 2) F (bit a.1 i) +
    algebraMap (ZMod 2) F (bit a.2 i) * QuadraticAlgebra.omega
def rowMatrix (a : Row) : Matrix9 := fun r c => decode a (9 * r.val + c.val)
def addRows (a b : Row) : Row := (a.1 ^^^ b.1, a.2 ^^^ b.2)
def omegaRow (a : Row) : Row := (a.2, a.1 ^^^ a.2)
def scalar : Fin 4 → F := ![0, 1, QuadraticAlgebra.omega, 1 + QuadraticAlgebra.omega]
def scaleRow (a : Fin 4) (r : Row) : Row :=
  ![(0, 0), r, omegaRow r, addRows r (omegaRow r)] a
def sumRows : List Row → Row
  | [] => (0, 0)
  | r :: rs => addRows r (sumRows rs)
def singleRow (r c : Fin 9) : Row := (2 ^ (9 * r.val + c.val), 0)
def packedCombine (rows : EquationIndex → Row) (w : List (EquationIndex × Fin 4)) : Row :=
  sumRows (w.map fun q => scaleRow q.2 (rows q.1))
lemma decode_zero (i : Nat) : decode (0, 0) i = 0 := by simp [decode, bit]
lemma decode_add (a b : Row) (i : Nat) :
    decode (addRows a b) i = decode a i + decode b i := by
  simp only [decode, addRows, bit_xor, map_add]
  ring
lemma decode_omega (a : Row) (i : Nat) :
    decode (omegaRow a) i = (QuadraticAlgebra.omega : F) * decode a i := by
  have hw : (QuadraticAlgebra.omega : F) ^ 2 = QuadraticAlgebra.omega + 1 := by
    decide +kernel
  simp only [decode, omegaRow, bit_xor, map_add]
  linear_combination -(algebraMap (ZMod 2) F (bit a.2 i)) * hw
lemma decode_scale (a : Fin 4) (r : Row) (i : Nat) :
    decode (scaleRow a r) i = scalar a * decode r i := by
  fin_cases a <;> simp [scaleRow, scalar, decode_zero, decode_add, decode_omega, add_mul]
lemma rowMatrix_zero : rowMatrix (0, 0) = 0 := by
  funext r c
  exact decode_zero _
lemma rowMatrix_add (a b : Row) : rowMatrix (addRows a b) = rowMatrix a + rowMatrix b := by
  funext r c
  exact decode_add a b _
lemma rowMatrix_scale (a : Fin 4) (r : Row) :
    rowMatrix (scaleRow a r) = scalar a • rowMatrix r := by
  funext i j
  exact decode_scale a r _
lemma rowMatrix_single (r c : Fin 9) : rowMatrix (singleRow r c) = unitRow r c := by
  have he (u v : Fin 9) : 9 * r.val + c.val = 9 * u.val + v.val ↔ u = r ∧ v = c := by
    constructor
    · intro h
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    · rintro ⟨rfl, rfl⟩; rfl
  funext u v
  simp [rowMatrix, singleRow, decode, bit, Nat.testBit_two_pow, he, unitRow]
def scalarCode (a : F) : Fin 4 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = QuadraticAlgebra.omega then 2 else 3
lemma scalar_scalarCode : ∀ a : F, scalar (scalarCode a) = a := by decide +kernel
def fieldRow (a : F) (r c : Fin 9) : Row := scaleRow (scalarCode a) (singleRow r c)
lemma evaluate_fieldRow (X : Matrix9) (a : F) (r c : Fin 9) :
    evaluate X (rowMatrix (fieldRow a r c)) = a * X r c := by
  rw [fieldRow, rowMatrix_scale, evaluate_smul, scalar_scalarCode, rowMatrix_single,
    evaluate_single]
lemma evaluate_sumRows (X : Matrix9) (rs : List Row) :
    evaluate X (rowMatrix (sumRows rs)) = (rs.map (fun r => evaluate X (rowMatrix r))).sum := by
  induction rs with
  | nil => simp [sumRows, rowMatrix_zero, evaluate]
  | cons r rs ih => simp only [sumRows, rowMatrix_add, evaluate_add, ih,
      List.map_cons, List.sum_cons]
def equationRow (A B : Matrix9) (r c : Fin 9) : Row :=
  sumRows ((List.finRange 9).map fun k =>
    addRows (fieldRow (A k c) r k) (fieldRow (B r k) k c))
lemma evaluate_equationRow (X A B : Matrix9) (r c : Fin 9) :
    evaluate X (rowMatrix (equationRow A B r c)) = (X * A) r c + (B * X) r c := by
  simp only [equationRow, evaluate_sumRows, List.map_map, Function.comp_def,
    rowMatrix_add, evaluate_add, evaluate_fieldRow]
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  simp only [Finset.sum_add_distrib, Matrix.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _
def packedEquations (M : Fin 4 → Matrix9) (e : EquationIndex) : Row :=
  equationRow (M (sourceIndex e.1)) (M (targetIndex e.1)) e.2.1 e.2.2

lemma packedCombine_zero (M : Fin 4 → Matrix9) (X : Matrix9)
    (h : ∀ k, X * M (sourceIndex k) = M (targetIndex k) * X)
    (rows : EquationIndex → Row) (hr : ∀ e, rows e = packedEquations M e)
    (w : List (EquationIndex × Fin 4)) :
    evaluate X (rowMatrix (packedCombine rows w)) = 0 := by
  induction w with
  | nil => simp [packedCombine, sumRows, rowMatrix_zero, evaluate]
  | cons q w ih =>
    simp only [packedCombine, List.map_cons, sumRows, rowMatrix_add,
      evaluate_add, rowMatrix_scale, evaluate_smul]
    change scalar q.2 * evaluate X (rowMatrix (rows q.1)) +
      evaluate X (rowMatrix (packedCombine rows w)) = 0
    rw [ih, add_zero, hr]
    unfold packedEquations
    rw [evaluate_equationRow, h, CharTwo.add_self_eq_zero, mul_zero]
lemma packed_column_zero (M : Fin 4 → Matrix9) (X : Matrix9)
    (h : ∀ k, X * M (sourceIndex k) = M (targetIndex k) * X)
    (rows : EquationIndex → Row) (hr : ∀ e, rows e = packedEquations M e)
    (w : Fin 9 → List (EquationIndex × Fin 4))
    (hw : ∀ r, packedCombine rows (w r) = singleRow r 0) :
    ∀ r, X r 0 = 0 := by
  intro r
  have hz := packedCombine_zero M X h rows hr (w r)
  rw [hw, rowMatrix_single, evaluate_single] at hz
  exact hz

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine.Simple.Certificate
