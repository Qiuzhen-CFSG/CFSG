module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Relations
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Reference
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
/-!
# Soundness of the Mathieu extension exclusion certificates

Packed rows represent linear forms in the 144 entries of an unknown binary
matrix. XOR is addition of these forms. Each encoded intertwining equation
vanishes on every solution; a row combination equal to a coordinate therefore
forces that coordinate to vanish. A whole zero column contradicts an involution.
The finite certificates and the checks against the literal catalogue actions
are supplied separately.

Source context: James (1973), Lemma 8.3, used in Aschbacher–Smith H.12.1(1).
This checker uses the packed-bit addition lemma of the Thompson certificates.
-/

@[expose] public noncomputable section
open scoped BigOperators
open Matrix
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.ExtensionExclusion.Certificate
open Thompson.BinaryMatrix
open PointModel Representation.SL3FourLocalCatalogue

def operators (i : CatalogueEntry) : Fin 5 → Matrix12 :=
  ![catalogueMatrix i (classicalWord 0), catalogueMatrix i (classicalWord 1),
    catalogueMatrix i (classicalWord 2), catalogueMatrix i (classicalWord 3),
    catalogueMatrix i Representation.SL3FourNaturalDual.centralScalar]

def evaluate (X : Matrix12) (a : Nat) : ZMod 2 :=
  ∑ r : Fin 12, ∑ c : Fin 12, bit a (12 * r.val + c.val) * X r c

lemma evaluate_xor (X : Matrix12) (a b : Nat) :
    evaluate X (a ^^^ b) = evaluate X a + evaluate X b := by
  simp only [evaluate, bit_xor, add_mul, Finset.sum_add_distrib]

lemma evaluate_zero (X : Matrix12) : evaluate X 0 = 0 := by
  simp [evaluate, bit]

lemma evaluate_single (X : Matrix12) (r c : Fin 12) :
    evaluate X (2 ^ (12 * r.val + c.val)) = X r c := by
  have he (u v : Fin 12) : 12 * r.val + c.val = 12 * u.val + v.val ↔ u = r ∧ v = c := by
    constructor
    · intro h
      have hu : u.val = r.val := by omega
      have hv : v.val = c.val := by omega
      exact ⟨Fin.ext hu, Fin.ext hv⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp [evaluate, bit, Nat.testBit_two_pow, he, ite_and]

def xorList : List Nat → Nat
  | [] => 0
  | a :: as => a ^^^ xorList as

lemma evaluate_xorList (X : Matrix12) (as : List Nat) :
    evaluate X (xorList as) = (as.map (evaluate X)).sum := by
  induction as with
  | nil => exact evaluate_zero X
  | cons a as ih => simp only [xorList, evaluate_xor, ih, List.map_cons, List.sum_cons]

def equationRow (A B : Matrix12) (r c : Fin 12) : Nat :=
  xorList ((List.finRange 12).map fun k =>
    (if A k c = 1 then 2 ^ (12 * r.val + k.val) else 0) ^^^
    (if B r k = 1 then 2 ^ (12 * k.val + c.val) else 0))

lemma evaluate_cond (X : Matrix12) (a : ZMod 2) (r c : Fin 12) :
    evaluate X (if a = 1 then 2 ^ (12 * r.val + c.val) else 0) = a * X r c := by
  have ha : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases ha a with rfl | rfl <;> simp [evaluate_zero, evaluate_single]

lemma evaluate_equationRow (X A B : Matrix12) (r c : Fin 12) :
    evaluate X (equationRow A B r c) = (X * A) r c + (B * X) r c := by
  simp only [equationRow, evaluate_xorList, List.map_map]
  simp only [Function.comp_def, evaluate_xor, evaluate_cond]
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  simp only [Finset.sum_add_distrib, Matrix.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

lemma equationRow_zero (X A B : Matrix12) (h : X * A = B * X) (r c : Fin 12) :
    evaluate X (equationRow A B r c) = 0 := by
  rw [evaluate_equationRow, h]
  exact CharTwo.add_self_eq_zero _

abbrev EquationIndex := Fin 3 × Fin 12 × Fin 12

def sourceIndex : Fin 3 → Fin 5 := ![0, 1, 4]
def targetIndex : Fin 3 → Fin 5 := ![2, 3, 4]

def equations (M : Fin 5 → Matrix12) (e : EquationIndex) : Nat :=
  equationRow (M (sourceIndex e.1)) (M (targetIndex e.1)) e.2.1 e.2.2

lemma operators_intertwine (i : CatalogueEntry) (X : Matrix12)
    (h : ExtensionEquations i X) :
    ∀ k, X * operators i (sourceIndex k) = operators i (targetIndex k) * X := by
  intro k
  fin_cases k
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.eq

lemma equations_zero (M : Fin 5 → Matrix12) (X : Matrix12)
    (h : ∀ k, X * M (sourceIndex k) = M (targetIndex k) * X) (e : EquationIndex) :
    evaluate X (equations M e) = 0 := equationRow_zero X _ _ (h e.1) _ _

lemma witness_zero (X : Matrix12) (rows : EquationIndex → Nat)
    (h : ∀ e, evaluate X (rows e) = 0) (w : List EquationIndex) :
    evaluate X (xorList (w.map rows)) = 0 := by
  rw [evaluate_xorList, List.map_map]
  simp [Function.comp_def, h]

lemma column_zero (M : Fin 5 → Matrix12) (X : Matrix12)
    (h : ∀ k, X * M (sourceIndex k) = M (targetIndex k) * X)
    (rows : EquationIndex → Nat) (hr : ∀ e, rows e = equations M e)
    (c : Fin 12) (w : Fin 12 → List EquationIndex)
    (hw : ∀ r, xorList ((w r).map rows) = 2 ^ (12 * r.val + c.val)) :
    ∀ r, X r c = 0 := by
  intro r
  have hz := witness_zero X rows (fun e => by rw [hr]; exact equations_zero M X h e) (w r)
  rw [hw, evaluate_single] at hz
  exact hz

lemma zero_column_contradiction (X : Matrix12) (h : X * X = 1) (c : Fin 12)
    (hc : ∀ r, X r c = 0) : False := by
  have he := congrArg (fun M : Matrix12 => M c c) h
  simp [Matrix.mul_apply, hc] at he
end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.ExtensionExclusion.Certificate
