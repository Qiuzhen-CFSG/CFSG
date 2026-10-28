module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.Flag

/-!
# Packed arithmetic for the natural Mathieu quotient certificates

Two natural numbers store the coefficients of 1 and omega in an F₄ vector.
XOR adds vectors, and multiplication by omega sends (a,b) to (b,a+b).
The decoding lemmas prove that the compact row products are genuine matrix
products over the field used by the literal induced representation.

This arithmetic checks the adapted coordinates documented in
`NaturalFiltration/source/README.md`; it assumes no numerical identities.
-/

@[expose] public section
open scoped Matrix
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration
namespace QuotientCertificate
abbrev Packed := ℕ × ℕ

def entry (x : Packed) (j : ℕ) : Field :=
  (bif x.1.testBit j then 1 else 0) +
    (bif x.2.testBit j then QuadraticAlgebra.omega else 0)
def add (x y : Packed) : Packed := (x.1 ^^^ y.1, x.2 ^^^ y.2)
def omegaMul (x : Packed) : Packed := (x.2, x.1 ^^^ x.2)
def scalar (a b : Bool) (x : Packed) : Packed :=
  add (if a then x else (0,0)) (if b then omegaMul x else (0,0))

lemma entry_zero (j : ℕ) : entry (0,0) j = 0 := by simp [entry]
lemma entry_add (x y : Packed) (j : ℕ) : entry (add x y) j = entry x j + entry y j := by
  simp only [entry, add, Nat.testBit_xor]
  cases x.1.testBit j <;> cases x.2.testBit j <;>
    cases y.1.testBit j <;> cases y.2.testBit j <;> decide
lemma entry_omegaMul (x : Packed) (j : ℕ) :
    entry (omegaMul x) j = QuadraticAlgebra.omega * entry x j := by
  simp only [entry, omegaMul, Nat.testBit_xor]
  cases x.1.testBit j <;> cases x.2.testBit j <;> decide
lemma entry_scalar (a b : Bool) (x : Packed) (j : ℕ) :
    entry (scalar a b x) j =
      ((bif a then 1 else 0) + (bif b then QuadraticAlgebra.omega else 0)) * entry x j := by
  cases a <;> cases b <;> simp [scalar, entry_add, entry_zero, entry_omegaMul, add_mul]

def sum : List Packed → Packed
  | [] => (0,0)
  | x :: xs => add x (sum xs)
lemma entry_sum (xs : List Packed) (j : ℕ) :
    entry (sum xs) j = (xs.map (fun x => entry x j)).sum := by
  induction xs with
  | nil => exact entry_zero j
  | cons x xs ih => simp only [sum, entry_add, List.map_cons, List.sum_cons, ih]

def rowProduct {n : ℕ} (x : Packed) (ys : Fin n → Packed) : Packed :=
  sum (List.ofFn fun k => scalar (x.1.testBit k.val) (x.2.testBit k.val) (ys k))
def matrix {m n : ℕ} (xs : Fin m → Packed) : Matrix (Fin m) (Fin n) Field :=
  fun i j => entry (xs i) j.val
lemma matrix_product {m n p : ℕ} (xs : Fin m → Packed) (ys : Fin n → Packed) :
    matrix (n := p) (fun i => rowProduct (xs i) ys) =
      matrix (n := n) xs * matrix ys := by
  funext i j
  change entry (rowProduct (xs i) ys) j.val = _
  rw [rowProduct, entry_sum, List.map_ofFn, List.sum_ofFn]
  change (∑ k : Fin n, entry (scalar ((xs i).1.testBit k.val) ((xs i).2.testBit k.val) (ys k)) j.val) = _
  simp only [Matrix.mul_apply, matrix]
  apply Finset.sum_congr rfl
  intro k _
  exact entry_scalar _ _ _ _

def identity {n : ℕ} (i : Fin n) : Packed := (2^i.val, 0)
lemma matrix_identity {n : ℕ} : matrix (n := n) (identity (n := n)) = 1 := by
  funext i j
  simp [matrix, identity, entry, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
end QuotientCertificate
end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration
