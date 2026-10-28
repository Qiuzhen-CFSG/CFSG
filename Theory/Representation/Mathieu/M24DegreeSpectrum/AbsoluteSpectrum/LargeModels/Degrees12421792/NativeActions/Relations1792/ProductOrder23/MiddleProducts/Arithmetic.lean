module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Arithmetic

/-!
# Bounded XOR checks for the two middle products

Split the right-hand row list into blocks of sixteen. The elementary binary
row evaluator depends only on the low bits used by its input list, and it
respects concatenation. These two facts prove equality with the published
sequential checker. The final block theorem assembles every left-hand row;
explicit base-65536 digits additionally avoid repeated large divisions.
Their bounds, lengths and reconstruction are checked, and `rowDigits_eq`
proves the exact row semantics. The concrete consumers are `MiddleProducts.fifth` and `MiddleProducts.tenth`.

Source: the addition chain for ATLAS M24G1-P1, word 2; see
`MiddleProducts/source/README.md` and `ProductOrder23/source/README.md`.
-/



@[expose] public section

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.MiddleProducts.Blocked

def small (a : Nat) : List Nat → Nat
  | [] => 0
  | b :: bs => ((a % 2) * b) ^^^ small (a / 2) bs

theorem small_eq (a : Nat) (bs : List Nat) : small a bs = skipRow a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    rw [small, skipRow, ih]
    have h := Nat.mod_lt a (by decide : 0 < 2)
    split <;> simp_all

theorem small_append (a : Nat) (xs ys : List Nat) :
    small a (xs ++ ys) = small a xs ^^^ small (a / 2 ^ xs.length) ys := by
  induction xs generalizing a with
  | nil => simp [small]
  | cons x xs ih =>
    simp only [List.cons_append, small, ih, List.length_cons, Nat.pow_succ',
      Nat.div_div_eq_div_mul, Nat.xor_assoc]

theorem small_mod (a : Nat) (xs : List Nat) :
    small (a % 2 ^ xs.length) xs = small a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, Nat.pow_succ', small,
      Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ih]

theorem small_zero (bs : List Nat) : small 0 bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [small, ih]

def smallFast (a : Nat) : List Nat → Nat
  | [] => 0
  | b :: bs => if a = 0 then 0 else ((a % 2) * b) ^^^ smallFast (a / 2) bs

theorem smallFast_eq (a : Nat) (bs : List Nat) : smallFast a bs = small a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    by_cases ha : a = 0
    · subst a
      simp [smallFast, small_zero]
    · simp only [smallFast, ha, if_false, small, ih]

def row (a : Nat) : List (List Nat) → Nat
  | [] => 0
  | b :: bs => if a = 0 then 0 else smallFast (a % 65536) b ^^^ row (a / 65536) bs

theorem row_eq (bs : List (List Nat)) (h : ∀ b ∈ bs, b.length = 16) (a : Nat) :
    row a bs = skipRow a bs.flatten := by
  rw [← small_eq]
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have hb := h b (by simp)
    have ht : ∀ b ∈ bs, b.length = 16 := by
      intro b hb
      exact h b (by simp [hb])
    by_cases ha : a = 0
    · subst a
      simp [row, small_zero]
    · simp only [row, ha, if_false, smallFast_eq, List.flatten_cons, small_append, ih ht]
      rw [← small_mod a b, hb]
      rfl

def checkRows : List Nat → List (List Nat) → List Nat → Bool
  | [], _, [] => true
  | a :: xs, bs, c :: zs => (row a bs == c) && checkRows xs bs zs
  | _, _, _ => false

theorem checkRows_sound (xs : List Nat) (bs : List (List Nat)) (zs : List Nat)
    (hb : ∀ b ∈ bs, b.length = 16) (h : checkRows xs bs zs = true) :
    checkSkip xs bs.flatten zs = true := by
  induction xs generalizing zs with
  | nil => cases zs <;> simp_all [checkRows, checkSkip]
  | cons a xs ih =>
    cases zs with
    | nil => simp [checkRows] at h
    | cons c zs =>
      simp only [checkRows, Bool.and_eq_true, beq_iff_eq] at h
      simp only [checkSkip, Bool.and_eq_true, beq_iff_eq]
      exact ⟨by rw [← row_eq bs hb a]; exact h.1, ih _ h.2⟩

def checkBlocks : List (List Nat) → List (List Nat) → List (List Nat) → Bool
  | [], _, [] => true
  | a :: xs, bs, c :: zs => checkRows a bs c && checkBlocks xs bs zs
  | _, _, _ => false

theorem checkBlocks_sound (xs bs zs : List (List Nat))
    (hb : ∀ b ∈ bs, b.length = 16) (h : checkBlocks xs bs zs = true) :
    checkSkip xs.flatten bs.flatten zs.flatten = true := by
  induction xs generalizing zs with
  | nil => cases zs <;> simp_all [checkBlocks, checkSkip]
  | cons a xs ih =>
    cases zs with
    | nil => simp [checkBlocks] at h
    | cons c zs =>
      simp only [checkBlocks, Bool.and_eq_true] at h
      exact Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Certificate.append
        a xs.flatten bs.flatten c zs.flatten (checkRows_sound _ _ _ hb h.1) (ih _ h.2)

/-- Reconstruction of an explicitly supplied base-65536 row. -/
def pack : List Nat → Nat
  | [] => 0
  | a :: ds => a + 65536 * pack ds

def rowDigits : List Nat → List (List Nat) → Nat
  | a :: ds, b :: bs => smallFast a b ^^^ rowDigits ds bs
  | _, _ => 0

def validDigits : List Nat → List (List Nat) → Bool
  | [], [] => true
  | a :: ds, b :: bs => (a < 65536) && (b.length == 16) && validDigits ds bs
  | _, _ => false

theorem rowDigits_eq (ds : List Nat) (bs : List (List Nat))
    (h : validDigits ds bs = true) :
    rowDigits ds bs = skipRow (pack ds) bs.flatten := by
  rw [← small_eq]
  induction ds generalizing bs with
  | nil => cases bs <;> simp_all [validDigits, pack, rowDigits, small]
  | cons a ds ih =>
    cases bs with
    | nil => simp [validDigits] at h
    | cons b bs =>
      simp only [validDigits, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      have hmod : (a + 65536 * pack ds) % 65536 = a := by omega
      have hdiv : (a + 65536 * pack ds) / 65536 = pack ds := by omega
      simp only [rowDigits, pack, List.flatten_cons, smallFast_eq, small_append, ih _ h.2]
      conv_rhs => lhs; rw [← small_mod _ b]
      rw [h.1.2]
      change small a b ^^^ small (pack ds) bs.flatten =
        small ((a + 65536 * pack ds) % 65536) b ^^^
          small ((a + 65536 * pack ds) / 65536) bs.flatten
      rw [hmod, hdiv]

def checkDigits : List (List Nat) → List Nat → List (List Nat) → List Nat → Bool
  | [], [], _, [] => true
  | d :: ds, a :: xs, bs, c :: zs =>
      validDigits d bs && (pack d == a) && (rowDigits d bs == c) && checkDigits ds xs bs zs
  | _, _, _, _ => false

theorem checkDigits_sound (ds : List (List Nat)) (xs : List Nat)
    (bs : List (List Nat)) (zs : List Nat) (h : checkDigits ds xs bs zs = true) :
    checkSkip xs bs.flatten zs = true := by
  induction ds generalizing xs zs with
  | nil => cases xs <;> cases zs <;> simp_all [checkDigits, checkSkip]
  | cons d ds ih =>
    cases xs with
    | nil => simp [checkDigits] at h
    | cons a xs =>
      cases zs with
      | nil => simp [checkDigits] at h
      | cons c zs =>
        simp only [checkDigits, Bool.and_eq_true, beq_iff_eq] at h
        simp only [checkSkip, Bool.and_eq_true, beq_iff_eq]
        exact ⟨by rw [← h.1.1.2, ← rowDigits_eq _ _ h.1.1.1]; exact h.1.2,
          ih _ _ h.2⟩

theorem checkRows_eq (xs : List Nat) (bs : List (List Nat)) (zs : List Nat)
    (hb : ∀ b ∈ bs, b.length = 16) :
    checkRows xs bs zs = checkSkip xs bs.flatten zs := by
  induction xs generalizing zs with
  | nil => cases zs <;> rfl
  | cons a xs ih =>
    cases zs with
    | nil => rfl
    | cons c zs => simp only [checkRows, checkSkip, row_eq bs hb a, ih]

theorem checkRows_of_digits (ds : List (List Nat)) (xs : List Nat)
    (bs : List (List Nat)) (zs : List Nat) (hb : ∀ b ∈ bs, b.length = 16)
    (h : checkDigits ds xs bs zs = true) : checkRows xs bs zs = true := by
  rw [checkRows_eq _ _ _ hb]
  exact checkDigits_sound _ _ _ _ h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.MiddleProducts.Blocked
