module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.Data

/-!
# Sound packed arithmetic for the dual induced flag

Two binary planes encode a column over F₄. XOR and a plane interchange
implement field addition and multiplication by omega. The decoding lemmas
turn finite integer certificates into genuine field matrix products.
This supports the induced-module calculation for Guralnick–Malle I,
Proposition 5.1, pp.15–16; candidate provenance is in `../source/README.md`.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FieldFlag.Packed
abbrev Row := ℕ × ℕ
def decode (r : Row) (i : ℕ) : F :=
  ⟨if r.1.testBit i then 1 else 0, if r.2.testBit i then 1 else 0⟩
def add (r s : Row) : Row := (r.1 ^^^ s.1, r.2 ^^^ s.2)
def omega (r : Row) : Row := (r.2, r.1 ^^^ r.2)
def scale (r : Row) (a b : Bool) : Row :=
  add (if a then r else (0,0)) (if b then omega r else (0,0))
def sum : List Row → Row
  | [] => (0,0)
  | r :: rs => add r (sum rs)
def combine {n : ℕ} (c : Fin n → Row) (r : Row) : Row :=
  sum (List.ofFn fun j => scale (c j) (r.1.testBit j) (r.2.testBit j))
def matrix {m n : ℕ} (c : Fin n → Row) : Matrix (Fin m) (Fin n) F :=
  fun i j => decode (c j) i
lemma decode_zero (i : ℕ) : decode (0,0) i = 0 := by simp [decode]; rfl
lemma decode_add (r s : Row) (i : ℕ) : decode (add r s) i = decode r i + decode s i := by
  unfold decode add
  simp only [Nat.testBit_xor]
  cases r.1.testBit i <;> cases r.2.testBit i <;>
    cases s.1.testBit i <;> cases s.2.testBit i <;> decide
lemma decode_omega (r : Row) (i : ℕ) :
    decode (omega r) i = decode r i * (QuadraticAlgebra.omega : F) := by
  unfold decode omega
  simp only [Nat.testBit_xor]
  cases r.1.testBit i <;> cases r.2.testBit i <;> decide
lemma decode_scale (r : Row) (a b : Bool) (i : ℕ) :
    decode (scale r a b) i = decode r i * (⟨if a then 1 else 0, if b then 1 else 0⟩ : F) := by
  cases a <;> cases b <;>
    simp only [scale, Bool.false_eq_true, ↓reduceIte, decode_add, decode_zero, decode_omega]
  · exact (mul_zero _).symm
  · exact zero_add _
  · exact (add_zero _).trans (mul_one _).symm
  · change decode r i + decode r i * QuadraticAlgebra.omega = decode r i * (1 + QuadraticAlgebra.omega)
    ring
lemma decode_sum (rs : List Row) (i : ℕ) :
    decode (sum rs) i = (rs.map fun r => decode r i).sum := by
  induction rs with
  | nil => exact decode_zero i
  | cons r rs ih => simp only [sum, decode_add, ih, List.map_cons, List.sum_cons]
lemma decode_combine {n : ℕ} (c : Fin n → Row) (r : Row) (i : ℕ) :
    decode (combine c r) i = ∑ j, decode (c j) i * decode r j := by
  rw [combine, decode_sum, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  exact decode_scale (c j) _ _ i
lemma decode_single (i j : ℕ) : decode (2^j,0) i = if i = j then 1 else 0 := by
  simp only [decode, Nat.testBit_two_pow, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]
  by_cases h : i = j <;> simp [h, eq_comm] <;> rfl
end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FieldFlag.Packed
