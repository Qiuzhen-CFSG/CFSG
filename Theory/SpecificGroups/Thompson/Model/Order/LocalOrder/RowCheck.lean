module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# Boolean row checking for the Thompson local matrices

Checking Boolean row equalities avoids constructing a dependent decision proof
at every row. Induction proves the checker sound, and the existing packed
multiplication theorem then gives the ordinary matrix equality. All concrete
Boolean checks are reduced by Lean's kernel.
-/

namespace Thompson.OrderCertificate.LocalMatrices

@[expose] public def checkRows (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => checkRows f n && f n

public theorem checkRows_spec (f : ℕ → Bool) (n : ℕ) :
    checkRows f n = true ↔ ∀ i, i < n → f i = true := by
  induction n with
  | zero => simp [checkRows]
  | succ n ih =>
    rw [checkRows, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact h i hlt
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

/-- Soundness of Boolean checking for a packed matrix product. -/
public theorem checked_mul (n : ℕ) (a b c : Array ℕ)
    (h : checkRows (fun i => BinaryMatrix.rowProduct a[i]! b n == c[i]!) n = true) :
    BinaryMatrix.decode n a * BinaryMatrix.decode n b = BinaryMatrix.decode n c := by
  apply BinaryMatrix.decode_mul
  intro i
  exact of_decide_eq_true ((checkRows_spec _ _).mp h i.val i.isLt)

/-- Soundness of Boolean checking for an inverse product. -/
public theorem checked_mul_one (n : ℕ) (a b : Array ℕ)
    (h : checkRows (fun i => BinaryMatrix.rowProduct a[i]! b n == 2 ^ i) n = true) :
    BinaryMatrix.decode n a * BinaryMatrix.decode n b = 1 := by
  apply BinaryMatrix.decode_mul_one
  intro i
  exact of_decide_eq_true ((checkRows_spec _ _).mp h i.val i.isLt)

/-- A row function representation avoids repeated linear array lookup in
kernel reduction of the inner multiplication loop. -/
@[expose] public def rowProductFn (a : ℕ) (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => rowProductFn a b k ^^^ (if a.testBit k then b k else 0)

private theorem rowProductFn_eq (a : ℕ) (b : Array ℕ) (f : ℕ → ℕ)
    (n : ℕ) (h : ∀ i, i < n → f i = b[i]!) :
    rowProductFn a f n = BinaryMatrix.rowProduct a b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rowProductFn, BinaryMatrix.rowProduct,
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

/-- Decode fixed-width rows from a single natural number. -/
@[expose] public def packedRow (n packed i : ℕ) : ℕ :=
  (packed >>> (n * i)) % 2 ^ n

/-- A checked packed lookup table and checked row products suffice. The
lookup certificate ties the faster representation to the original array. -/
public theorem checked_mul_packed (n : ℕ) (a b c : Array ℕ) (leftPacked packed : ℕ)
    (ha : checkRows (fun i => packedRow n leftPacked i == a[i]!) n = true)
    (hb : checkRows (fun i => packedRow n packed i == b[i]!) n = true)
    (hm : checkRows (fun i => rowProductFn (packedRow n leftPacked i) (packedRow n packed) n == c[i]!) n = true) :
    BinaryMatrix.decode n a * BinaryMatrix.decode n b = BinaryMatrix.decode n c := by
  apply BinaryMatrix.decode_mul
  intro i
  rw [← rowProductFn_eq a[i.val]! b (packedRow n packed) n
    (fun j hj => of_decide_eq_true ((checkRows_spec _ _).mp hb j hj))]
  have he : packedRow n leftPacked i.val = a[i.val]! :=
    of_decide_eq_true ((checkRows_spec _ _).mp ha i.val i.isLt)
  rw [← he]
  exact of_decide_eq_true ((checkRows_spec _ _).mp hm i.val i.isLt)

public theorem checked_mul_one_packed (n : ℕ) (a b : Array ℕ) (leftPacked packed : ℕ)
    (ha : checkRows (fun i => packedRow n leftPacked i == a[i]!) n = true)
    (hb : checkRows (fun i => packedRow n packed i == b[i]!) n = true)
    (hm : checkRows (fun i => rowProductFn (packedRow n leftPacked i) (packedRow n packed) n == 2 ^ i) n = true) :
    BinaryMatrix.decode n a * BinaryMatrix.decode n b = 1 := by
  apply BinaryMatrix.decode_mul_one
  intro i
  rw [← rowProductFn_eq a[i.val]! b (packedRow n packed) n
    (fun j hj => of_decide_eq_true ((checkRows_spec _ _).mp hb j hj))]
  have he : packedRow n leftPacked i.val = a[i.val]! :=
    of_decide_eq_true ((checkRows_spec _ _).mp ha i.val i.isLt)
  rw [← he]
  exact of_decide_eq_true ((checkRows_spec _ _).mp hm i.val i.isLt)

end Thompson.OrderCertificate.LocalMatrices
