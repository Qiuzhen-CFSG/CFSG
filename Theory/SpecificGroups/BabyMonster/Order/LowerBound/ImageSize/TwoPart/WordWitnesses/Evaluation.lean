module
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.TwoPart.Candidates
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# Exact packed evaluation of Baby Monster group words

Expressions in the fixed generators evaluate inside `standardImage`. Independently,
each expression computes a vector of packed binary rows. The proof identifies its
entries with the underlying unit matrix by induction on the expression, using the
proved XOR multiplication checker. Inverses reverse products; the inverse leaves
are `a` and `b²`, so only the square/cube hypotheses are needed.

The input matrices and bit convention come from `LowerBound/source/README.md`.
This module certifies evaluation, not the order or independence of any word family.
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.TwoPart.WordWitnesses

/-- Straight-line group expressions in the two fixed generators. -/
inductive Word where
  | one
  | a
  | b
  | mul (x y : Word)
  | inv (x : Word)
  | pow (x : Word) (n : Nat)
  deriving Repr

def Word.eval {G : Type*} [Group G] (a b : G) : Word → G
  | .one => 1
  | .a => a
  | .b => b
  | .mul x y => x.eval a b * y.eval a b
  | .inv x => (x.eval a b)⁻¹
  | .pow x n => (x.eval a b) ^ n

abbrev Rows := Vector Nat 4370

def decode (r : Rows) : AtlasMatrix :=
  fun i j => Thompson.BinaryMatrix.bit (r.get i) j.val

def rowsOne : Rows := Vector.ofFn (fun i => 2 ^ i.val)
def rowsA : Rows := Vector.ofFn atlasARow
def rowsB : Rows := Vector.ofFn atlasBRow

def rowsMul (r s : Rows) : Rows :=
  Vector.ofFn (fun i => Thompson.BinaryMatrix.rowProduct (r.get i) s.toArray 4370)

theorem decode_rowsOne : decode rowsOne = 1 := by
  ext i j
  simp [decode, rowsOne, Vector.get, Fin.cast, Thompson.BinaryMatrix.bit,
    Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem decode_rowsA : decode rowsA = atlasA := by
  ext i j
  simp [decode, rowsA, Vector.get, Fin.cast, Thompson.BinaryMatrix.bit, atlasA]

theorem decode_rowsB : decode rowsB = atlasB := by
  ext i j
  simp [decode, rowsB, Vector.get, Fin.cast, Thompson.BinaryMatrix.bit, atlasB]

theorem decode_rowsMul (r s : Rows) : decode (rowsMul r s) = decode r * decode s := by
  have aux (v : Rows) : Thompson.BinaryMatrix.decode 4370 v.toArray = decode v := by
    ext i j
    simp [Thompson.BinaryMatrix.decode, decode, Vector.get]
  rw [← aux r, ← aux s, ← aux (rowsMul r s)]
  symm
  apply Thompson.BinaryMatrix.decode_mul
  intro i
  simp [rowsMul, Vector.get]

/-- Repeated packed multiplication; zero powers give the identity matrix. -/
def rowsPow (r : Rows) : Nat → Rows
  | 0 => rowsOne
  | n + 1 => rowsMul (rowsPow r n) r

theorem decode_rowsPow (r : Rows) (n : Nat) :
    decode (rowsPow r n) = decode r ^ n := by
  induction n with
  | zero => exact decode_rowsOne
  | succ n ih => rw [rowsPow, decode_rowsMul, ih, pow_succ]

/-- Packed forward and inverse evaluation. The inverse leaves use only the
square/cube hypotheses, not a matrix inversion algorithm. -/
def Word.rows : Word → Bool → Rows
  | .one, _ => rowsOne
  | .a, _ => rowsA
  | .b, false => rowsB
  | .b, true => rowsMul rowsB rowsB
  | .mul x y, false => rowsMul (x.rows false) (y.rows false)
  | .mul x y, true => rowsMul (y.rows true) (x.rows true)
  | .inv x, e => x.rows (!e)
  | .pow x n, e => rowsPow (x.rows e) n

def Word.element (w : Word) (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    standardImage ha hb := w.eval (TwoPart.a ha hb) (TwoPart.b ha hb)

def matrix (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (g : standardImage ha hb) : AtlasMatrix := (g.val : AtlasMatrix)

theorem matrix_mul (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (g h : standardImage ha hb) : matrix ha hb (g * h) = matrix ha hb g * matrix ha hb h := rfl

theorem Word.decode_rows (w : Word) (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (e : Bool) : decode (w.rows e) =
      matrix ha hb (if e then (w.element ha hb)⁻¹ else w.element ha hb) := by
  induction w generalizing e with
  | one => cases e <;> simpa [Word.rows, Word.element, Word.eval, matrix] using decode_rowsOne
  | a => cases e <;> exact decode_rowsA
  | b =>
    cases e
    · exact decode_rowsB
    · rw [Word.rows, decode_rowsMul, decode_rowsB]
      change atlasB * atlasB = atlasB ^ 2
      exact (pow_two atlasB).symm
  | mul x y hx hy =>
    cases e <;> simp only [Word.rows, decode_rowsMul, hx, hy, Bool.false_eq_true,
      if_false, if_true, Word.element, Word.eval, mul_inv_rev, matrix_mul]
  | pow x n hx =>
    cases e <;> simp only [Word.rows, decode_rowsPow, hx, Bool.false_eq_true,
      if_false, if_true, Word.element, Word.eval]
    all_goals rfl
  | inv x hx =>
    cases e
    · simpa [Word.rows, Word.element, Word.eval] using hx true
    · simpa [Word.rows, Word.element, Word.eval] using hx false

/-- The entrywise specification consumed by matrix certificate proofs. -/
theorem Word.matrix_entry (w : Word) (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (r c : Fin 4370) : matrix ha hb (w.element ha hb) r c =
      if ((w.rows false).get r).testBit c.val then 1 else 0 := by
  have h := congrArg (fun m : AtlasMatrix => m r c) (w.decode_rows ha hb false)
  exact h.symm


end BabyMonster.OrderLowerBound.TwoPart.WordWitnesses
