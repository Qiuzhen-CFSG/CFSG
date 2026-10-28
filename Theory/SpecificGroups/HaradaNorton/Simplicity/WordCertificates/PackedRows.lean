module

public import Theory.SpecificGroups.HaradaNorton.MatrixData
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Packed row arithmetic over the field with five elements

Three natural numbers hold the binary digits of all entries in a row. Boolean
circuits therefore add all columns simultaneously. The circuit first adds the
three-bit inputs, twice replaces a carry of weight eight by weight three, and
then reduces the possible values five, six and seven. Its field interpretation
is checked on the 64 possible pairs of three-bit inputs, without any assumption
that the inputs are canonical. Induction identifies the packed row product
with the ordinary matrix product.

This checker is used for the concrete ATLAS HN word certificates. It makes no
assumption about the ATLAS group or the matrices being invertible. Matrix
provenance: `../../MatrixSources.md`.
-/

@[expose] public section
namespace HaradaNorton.WordCertificates

/-- Three bit planes, least significant first. -/
structure Row where
  low : Nat
  mid : Nat
  high : Nat
  deriving DecidableEq

def bit (n j : Nat) : ZMod 5 := if n.testBit j then 1 else 0
def entry (r : Row) (j : Nat) : ZMod 5 := bit r.low j + 2 * bit r.mid j + 4 * bit r.high j

def foldCarry (x : Row) (c : Nat) : Row × Nat :=
  let d0 := x.low &&& c
  let d1 := (x.mid &&& c) ||| ((x.mid ^^^ c) &&& d0)
  (⟨x.low ^^^ c, x.mid ^^^ c ^^^ d0, x.high ^^^ d1⟩, x.high &&& d1)

def add (a b : Row) : Row :=
  let c0 := a.low &&& b.low
  let c1 := (a.mid &&& b.mid) ||| ((a.mid ^^^ b.mid) &&& c0)
  let c2 := (a.high &&& b.high) ||| ((a.high ^^^ b.high) &&& c1)
  let t : Row := ⟨a.low ^^^ b.low, a.mid ^^^ b.mid ^^^ c0, a.high ^^^ b.high ^^^ c1⟩
  let u := foldCarry t c2
  let v := (foldCarry u.1 u.2).1
  let h := v.high &&& (v.low ||| v.mid)
  ⟨v.low ^^^ h, v.mid ^^^ ((v.high &&& v.mid) ^^^ (v.high &&& v.mid &&& v.low)), v.high ^^^ h⟩

private theorem add_bits : ∀ a0 a1 a2 b0 b1 b2 : Bool,
    entry (add ⟨a0.toNat, a1.toNat, a2.toNat⟩ ⟨b0.toNat, b1.toNat, b2.toNat⟩) 0 =
    entry ⟨a0.toNat, a1.toNat, a2.toNat⟩ 0 + entry ⟨b0.toNat, b1.toNat, b2.toNat⟩ 0 := by
  decide +kernel

lemma entry_add (a b : Row) (j : Nat) : entry (add a b) j = entry a j + entry b j := by
  have h := add_bits (a.low.testBit j) (a.mid.testBit j) (a.high.testBit j)
    (b.low.testBit j) (b.mid.testBit j) (b.high.testBit j)
  simpa only [entry, bit, add, foldCarry, Nat.testBit_xor, Nat.testBit_and,
    Nat.testBit_or, Nat.testBit_bool_toNat, decide_true, Bool.true_and] using h

def zero : Row := ⟨0, 0, 0⟩
lemma entry_zero (j : Nat) : entry zero j = 0 := by simp [entry, zero, bit]

def value (a : Row) (j : Nat) : Nat :=
  (a.low.testBit j).toNat + 2 * (a.mid.testBit j).toNat + 4 * (a.high.testBit j).toNat

lemma value_cast (a : Row) (j : Nat) : (value a j : ZMod 5) = entry a j := by
  simp only [value, entry, bit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  cases a.low.testBit j <;> cases a.mid.testBit j <;> cases a.high.testBit j <;> rfl

def scale (a : Nat) (b : Row) : Row :=
  match a with
  | 0 => zero
  | n + 1 => add (scale n b) b

lemma entry_scale (a : Nat) (b : Row) (j : Nat) : entry (scale a b) j = a * entry b j := by
  induction a with
  | zero => simp [scale, entry_zero]
  | succ n ih => simp only [scale, entry_add, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

def rowProduct (a : Row) (b : Nat → Row) : Nat → Row
  | 0 => zero
  | n + 1 => add (rowProduct a b n) (scale (value a n) (b n))

lemma entry_rowProduct (a : Row) (b : Nat → Row) (n j : Nat) :
    entry (rowProduct a b n) j = ∑ k ∈ Finset.range n, entry a k * entry (b k) j := by
  induction n with
  | zero => simp [rowProduct, entry_zero]
  | succ n ih => rw [rowProduct, entry_add, ih, entry_scale, value_cast, Finset.sum_range_succ]

def decode (a : Nat → Row) : Matrix133 := fun i j => entry (a i.val) j.val

/-- A checked packed product is an equality of the decoded matrices. -/
lemma decode_mul (a b c : Nat → Row)
    (h : ∀ i : Fin 133, rowProduct (a i.val) b 133 = c i.val) :
    decode a * decode b = decode c := by
  ext i j
  change (∑ k : Fin 133, entry (a i.val) k.val * entry (b k.val) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => entry (a i.val) k * entry (b k) j.val),
    ← entry_rowProduct, h i]
  rfl

def oneRows (i : Nat) : Row := ⟨2 ^ i, 0, 0⟩
lemma decode_oneRows : decode oneRows = 1 := by
  ext i j
  simp [decode, entry, bit, oneRows, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff,
    eq_comm]

end HaradaNorton.WordCertificates
