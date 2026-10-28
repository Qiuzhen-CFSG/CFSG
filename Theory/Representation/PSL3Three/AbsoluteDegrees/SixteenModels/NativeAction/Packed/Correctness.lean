module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Transport

/-!
# Correctness of packed GF16 matrix multiplication

The proof applies to arbitrary natural-number rows, without a 64-bit bound.
Extraction of a nibble commutes with XOR and AND. Bounds on the lower part of
each fixed mask show that multiplying the masked parts by two and three causes
no carry across nibble boundaries. This identifies the packed shift with
multiplication by X modulo X⁴+X+1. The four-bit scalar formula and induction on
the row scan then give the literal encoded matrix product.

The coefficient convention is that of ATLAS L33G1-f16r16aB0, with source and
attribution in `SixteenModels.Data`. `Certificate.actionsExist` applies the
result to the actual native-edge and action-transport consumer; only the
independently constructed finite table certificate remains an input.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed

private theorem pow16 (j : ℕ) : 16 ^ j = 2 ^ (4 * j) := by
  exact (Nat.pow_mul 2 4 j).symm

/-- A small remainder cannot carry into the quotient when multiplied. -/
private theorem div_mul_no_carry (a c q : ℕ) (hq : 0 < q)
    (h : a % q * c < q) : a * c / q = a / q * c := by
  calc
    a * c / q = (a % q * c + q * (a / q * c)) / q := by
      congr 1
      rw [← Nat.mul_assoc, ← Nat.add_mul, Nat.mod_add_div]
    _ = a / q * c := by
      rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt h, Nat.zero_add]

private theorem digit_and (a b : ℕ) (j : Fin 16) :
    (digit (a &&& b) j).val = (digit a j).val &&& (digit b j).val := by
  simp only [digit, pow16, Nat.and_div_two_pow]
  exact Nat.and_mod_two_pow (n := 4)

private theorem digit_xor (a b : ℕ) (j : Fin 16) :
    digit (a ^^^ b) j = addCode (digit a j) (digit b j) := by
  apply Fin.ext
  simp only [digit, addCode, pow16, Nat.xor_div_two_pow]
  exact Nat.xor_mod_two_pow (n := 4)

/-- Mask bounds suffice; no upper bound on the row is used. -/
private theorem digit_mask_mul (a m c : ℕ) (j : Fin 16)
    (h : m % 16 ^ j.val * c < 16 ^ j.val) :
    (digit ((a &&& m) * c) j).val =
      ((digit a j).val &&& (digit m j).val) * c % 16 := by
  have hrem : (a &&& m) % 16 ^ j.val ≤ m % 16 ^ j.val := by
    rw [pow16, Nat.and_mod_two_pow]
    exact Nat.and_le_right
  have hc := div_mul_no_carry (a &&& m) c (16 ^ j.val) (by positivity)
    (lt_of_le_of_lt (Nat.mul_le_mul_right c hrem) h)
  change ((a &&& m) * c / 16 ^ j.val) % 16 = _
  rw [hc, Nat.mul_mod]
  rw [show (a &&& m) / 16 ^ j.val % 16 =
    (digit a j).val &&& (digit m j).val from digit_and a m j]
  simp only [Nat.mul_mod, Nat.mod_mod]

private theorem mask7 (j : Fin 16) :
    (digit 8608480567731124087 j).val = 7 ∧
      8608480567731124087 % 16 ^ j.val * 2 < 16 ^ j.val := by
  have h : ∀ j : Fin 16, (digit 8608480567731124087 j).val = 7 ∧
      8608480567731124087 % 16 ^ j.val * 2 < 16 ^ j.val := by decide
  exact h j

private theorem mask1 (j : Fin 16) :
    (digit 1229782938247303441 j).val = 1 ∧
      1229782938247303441 % 16 ^ j.val * 3 < 16 ^ j.val := by
  have h : ∀ j : Fin 16, (digit 1229782938247303441 j).val = 1 ∧
      1229782938247303441 % 16 ^ j.val * 3 < 16 ^ j.val := by decide
  exact h j

private theorem digit_shiftRight_three (a : ℕ) (j : Fin 16) :
    (digit (a >>> 3) j).val &&& 1 = (digit a j).val / 8 := by
  simp only [digit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm 8, ← Nat.div_div_eq_div_mul]
  omega

private theorem digit_shift (a : ℕ) (j : Fin 16) :
    digit (shift a) j = shiftCode (digit a j) := by
  have hshift : ∀ b : Fin 16,
      (((b.val &&& 7) * 2 % 16) ^^^ (b.val / 8 * 3 % 16)) = (shiftCode b).val := by
    decide
  apply Fin.ext
  unfold shift
  rw [digit_xor]
  change (digit ((a &&& 8608480567731124087) <<< 1) j).val ^^^
    (digit (((a >>> 3) &&& 1229782938247303441) * 3) j).val = _
  rw [Nat.shiftLeft_eq, digit_mask_mul _ _ _ _ (mask7 j).2,
    digit_mask_mul _ _ _ _ (mask1 j).2, (mask7 j).1, (mask1 j).1,
    digit_shiftRight_three]
  exact hshift (digit a j)

private theorem digit_zero (j : Fin 16) : digit 0 j = 0 := by
  apply Fin.ext
  simp [digit]

/-- The four-bit polynomial expansion, checked against the published product table. -/
private theorem scalar_formula : ∀ a b : Fin 16,
    addCode (addCode (addCode
      (if a.val.testBit 0 then b else 0)
      (if a.val.testBit 1 then shiftCode b else 0))
      (if a.val.testBit 2 then shiftCode (shiftCode b) else 0))
      (if a.val.testBit 3 then shiftCode (shiftCode (shiftCode b)) else 0) =
    mulCode a b := by decide

private theorem digit_scale (a : Fin 16) (r : ℕ) (j : Fin 16) :
    digit (scale a r) j = mulCode a (digit r j) := by
  have digit_ite (b : Bool) (s t : ℕ) :
      digit (if b then s else t) j = if b then digit s j else digit t j := by
    cases b <;> rfl
  simp only [scale, digit_xor, digit_ite, digit_zero, digit_shift]
  exact scalar_formula a (digit r j)

/-- Each recursive step consumes precisely the next base-sixteen coefficient. -/
private theorem digit_scan_ofFn (n : ℕ) (r : ℕ) (ys : Fin n → ℕ) (j : Fin 16) :
    digit (scan r (List.ofFn ys)) j = sumCode (List.ofFn (fun k : Fin n =>
      mulCode ⟨r / 16 ^ k.val % 16, Nat.mod_lt _ (by decide)⟩ (digit (ys k) j))) := by
  induction n generalizing r with
  | zero => simp [List.ofFn_zero, scan, digit_zero, sumCode]
  | succ n ih =>
    rw [List.ofFn_succ, scan, digit_xor, digit_scale, ih, List.ofFn_succ, sumCode]
    simp only [Fin.val_zero, Nat.pow_zero, Nat.div_one]
    congr 1
    apply congrArg sumCode
    apply congrArg List.ofFn
    funext k
    simp only [Fin.val_succ, Nat.pow_succ', Nat.div_div_eq_div_mul]

private theorem digit_row (r : ℕ) (y : Rows) (j : Fin 16) :
    digit (row r y) j = sumCode (List.ofFn (fun k : Fin 16 =>
      mulCode (digit r k) (digit (y.get k) j))) := by
  have hlist : y.toList = List.ofFn (fun k => y.get k) := by
    rw [← Vector.toList_ofFn]
    exact congrArg Vector.toList Vector.ofFn_getElem.symm
  rw [row, hlist]
  exact digit_scan_ofFn 16 r (fun k => y.get k) j

/-- Packed multiplication decodes to the literal row-by-column GF16 product. -/
theorem multiplicationCorrect : MultiplicationCorrect := by
  intro x y
  funext i j
  change digit ((Vector.ofFn (fun k => row (x.get k) y)).get i) j = _
  have hget : (Vector.ofFn (fun k => row (x.get k) y)).get i = row (x.get i) y := by
    simp [Vector.get, Fin.cast]
  rw [hget]
  exact digit_row (x.get i) y j

universe v

/-- Apply arithmetic correctness to any native packed edge certificate.
This discharges the arithmetic premise of `Certificate.toEdgeTable`, then uses
its exact native matrices and quotient transport to construct the marked action. -/
theorem Certificate.actionsExist (E : Certificate) : ActionsExist.{v} :=
  actionsExist_of_edgeTable (E.toEdgeTable multiplicationCorrect)

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed
