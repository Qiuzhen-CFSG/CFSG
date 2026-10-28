module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Data
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar
/-!
# Binary arithmetic for the degree-sixteen density certificate

The four-bit codes represent binary polynomials in a root of `X⁴+X+1`.
Addition is XOR; the multiplication table is checked against binary shift
and addition. Evaluation preserves these operations over every characteristic-two
field with `t⁴=t+1`, in every universe. Matrix and vector checks therefore
transport to the literal matrices of `SixteenModels.Data`.

This checker supplies the rank-one and orbit certificates below. No finite-field
structure or external computation is trusted. Source matrices and attribution:
ATLAS L33G1-f16r16aB0, as recorded in `SixteenModels.Data`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density

@[expose] def addCode (a b : Fin 16) : Fin 16 :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 4) a.isLt b.isLt⟩
@[expose] def shiftCode : Fin 16 → Fin 16 :=
  ![0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13]
@[expose] def mulTable : Matrix (Fin 16) (Fin 16) (Fin 16) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15;
    0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13;
    0, 3, 6, 5, 12, 15, 10, 9, 11, 8, 13, 14, 7, 4, 1, 2;
    0, 4, 8, 12, 3, 7, 11, 15, 6, 2, 14, 10, 5, 1, 13, 9;
    0, 5, 10, 15, 7, 2, 13, 8, 14, 11, 4, 1, 9, 12, 3, 6;
    0, 6, 12, 10, 11, 13, 7, 1, 5, 3, 9, 15, 14, 8, 2, 4;
    0, 7, 14, 9, 15, 8, 1, 6, 13, 10, 3, 4, 2, 5, 12, 11;
    0, 8, 3, 11, 6, 14, 5, 13, 12, 4, 15, 7, 10, 2, 9, 1;
    0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14;
    0, 10, 7, 13, 14, 4, 9, 3, 15, 5, 8, 2, 1, 11, 6, 12;
    0, 11, 5, 14, 10, 1, 15, 4, 7, 12, 2, 9, 13, 6, 8, 3;
    0, 12, 11, 7, 5, 9, 14, 2, 10, 6, 1, 13, 15, 3, 4, 8;
    0, 13, 9, 4, 1, 12, 8, 5, 2, 15, 11, 6, 3, 14, 10, 7;
    0, 14, 15, 1, 13, 3, 2, 12, 9, 7, 6, 8, 4, 10, 11, 5;
    0, 15, 13, 2, 9, 6, 4, 11, 1, 14, 12, 3, 8, 7, 5, 10]
@[expose] def mulCode (a b : Fin 16) : Fin 16 := mulTable a b

theorem mulCode_formula : ∀ a b : Fin 16, mulCode a b =
    addCode (addCode (if b.val.testBit 0 then a else 0)
      (if b.val.testBit 1 then shiftCode a else 0))
    (addCode (if b.val.testBit 2 then shiftCode (shiftCode a) else 0)
      (if b.val.testBit 3 then shiftCode (shiftCode (shiftCode a)) else 0)) := by
  decide +kernel

variable {F : Type*} [Field F] [CharP F 2]
@[expose] def bitValue (b : Bool) : F := if b then 1 else 0

theorem bitValue_xor (a b : Bool) :
    bitValue (F := F) (a ^^ b) = bitValue a + bitValue b := by
  cases a <;> cases b <;> simp [bitValue, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem coefficient_bits (t : F) (a : Fin 16) :
    coefficient t a = bitValue (a.val.testBit 0) +
      t * bitValue (a.val.testBit 1) + t ^ 2 * bitValue (a.val.testBit 2) +
      t ^ 3 * bitValue (a.val.testBit 3) := by
  fin_cases a
  · change 0 = 0 + t * 0 + t ^ 2 * 0 + t ^ 3 * 0
    ring
  · change 1 = 1 + t * 0 + t ^ 2 * 0 + t ^ 3 * 0
    ring
  · change t = 0 + t * 1 + t ^ 2 * 0 + t ^ 3 * 0
    ring
  · change t + 1 = 1 + t * 1 + t ^ 2 * 0 + t ^ 3 * 0
    ring
  · change t ^ 2 = 0 + t * 0 + t ^ 2 * 1 + t ^ 3 * 0
    ring
  · change t ^ 2 + 1 = 1 + t * 0 + t ^ 2 * 1 + t ^ 3 * 0
    ring
  · change t ^ 2 + t = 0 + t * 1 + t ^ 2 * 1 + t ^ 3 * 0
    ring
  · change t ^ 2 + t + 1 = 1 + t * 1 + t ^ 2 * 1 + t ^ 3 * 0
    ring
  · change t ^ 3 = 0 + t * 0 + t ^ 2 * 0 + t ^ 3 * 1
    ring
  · change t ^ 3 + 1 = 1 + t * 0 + t ^ 2 * 0 + t ^ 3 * 1
    ring
  · change t ^ 3 + t = 0 + t * 1 + t ^ 2 * 0 + t ^ 3 * 1
    ring
  · change t ^ 3 + t + 1 = 1 + t * 1 + t ^ 2 * 0 + t ^ 3 * 1
    ring
  · change t ^ 3 + t ^ 2 = 0 + t * 0 + t ^ 2 * 1 + t ^ 3 * 1
    ring
  · change t ^ 3 + t ^ 2 + 1 = 1 + t * 0 + t ^ 2 * 1 + t ^ 3 * 1
    ring
  · change t ^ 3 + t ^ 2 + t = 0 + t * 1 + t ^ 2 * 1 + t ^ 3 * 1
    ring
  · change t ^ 3 + t ^ 2 + t + 1 = 1 + t * 1 + t ^ 2 * 1 + t ^ 3 * 1
    ring

theorem coefficient_add (t : F) (a b : Fin 16) :
    coefficient t (addCode a b) = coefficient t a + coefficient t b := by
  simp only [coefficient_bits, addCode, Nat.testBit_xor, bitValue_xor]
  ring

theorem coefficient_shift (t : F) (ht : t ^ 4 = t + 1) (a : Fin 16) :
    coefficient t (shiftCode a) = t * coefficient t a := by
  fin_cases a
  · change 0 = t * (0)
    ring
  · change t = t * (1)
    ring
  · change t ^ 2 = t * (t)
    ring
  · change t ^ 2 + t = t * (t + 1)
    ring
  · change t ^ 3 = t * (t ^ 2)
    ring
  · change t ^ 3 + t = t * (t ^ 2 + 1)
    ring
  · change t ^ 3 + t ^ 2 = t * (t ^ 2 + t)
    ring
  · change t ^ 3 + t ^ 2 + t = t * (t ^ 2 + t + 1)
    ring
  · change t + 1 = t * (t ^ 3)
    ring_nf
    rw [ht]
    ring_nf
  · change 1 = t * (t ^ 3 + 1)
    ring_nf
    rw [ht]
    ring_nf
    reduce_mod_char!
  · change t ^ 2 + t + 1 = t * (t ^ 3 + t)
    ring_nf
    rw [ht]
    ring_nf
  · change t ^ 2 + 1 = t * (t ^ 3 + t + 1)
    ring_nf
    rw [ht]
    ring_nf
    reduce_mod_char!
  · change t ^ 3 + t + 1 = t * (t ^ 3 + t ^ 2)
    ring_nf
    rw [ht]
    ring_nf
  · change t ^ 3 + 1 = t * (t ^ 3 + t ^ 2 + 1)
    ring_nf
    rw [ht]
    ring_nf
    reduce_mod_char!
  · change t ^ 3 + t ^ 2 + t + 1 = t * (t ^ 3 + t ^ 2 + t)
    ring_nf
    rw [ht]
    ring_nf
  · change t ^ 3 + t ^ 2 + 1 = t * (t ^ 3 + t ^ 2 + t + 1)
    ring_nf
    rw [ht]
    ring_nf
    reduce_mod_char!

omit [CharP F 2] in
theorem coefficient_zero (t : F) : coefficient t 0 = 0 := rfl

theorem coefficient_mul (t : F) (ht : t ^ 4 = t + 1) (a b : Fin 16) :
    coefficient t (mulCode a b) = coefficient t a * coefficient t b := by
  rw [mulCode_formula]
  simp only [coefficient_add, apply_ite (coefficient t), coefficient_shift t ht,
    coefficient_zero]
  rw [coefficient_bits t b]
  unfold bitValue
  split_ifs <;> ring



@[expose] def codeSum : List (Fin 16) → Fin 16
  | [] => 0
  | a :: as => addCode a (codeSum as)

@[expose] def codeProduct (M N : Matrix (Fin 16) (Fin 16) (Fin 16)) :
    Matrix (Fin 16) (Fin 16) (Fin 16) :=
  fun i j => codeSum (List.ofFn (fun k => mulCode (M i k) (N k j)))

@[expose] def codeMulVec (M : Matrix (Fin 16) (Fin 16) (Fin 16)) (x : Fin 16 → Fin 16) :
    Fin 16 → Fin 16 :=
  fun i => codeSum (List.ofFn (fun k => mulCode (M i k) (x k)))

@[expose] def codeVecMul (x : Fin 16 → Fin 16) (M : Matrix (Fin 16) (Fin 16) (Fin 16)) :
    Fin 16 → Fin 16 :=
  fun j => codeSum (List.ofFn (fun k => mulCode (x k) (M k j)))

@[expose] def evalMatrix (t : F) (M : Matrix (Fin 16) (Fin 16) (Fin 16)) :
    Matrix (Fin 16) (Fin 16) F := M.map (coefficient t)

@[expose] def evalVector (t : F) (x : Fin 16 → Fin 16) : Fin 16 → F := coefficient t ∘ x

theorem coefficient_sum (t : F) (xs : List (Fin 16)) :
    coefficient t (codeSum xs) = (xs.map (coefficient t)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [codeSum, coefficient_add, ih, List.map_cons, List.sum_cons]

theorem eval_product (t : F) (ht : t ^ 4 = t + 1)
    (M N : Matrix (Fin 16) (Fin 16) (Fin 16)) :
    evalMatrix t (codeProduct M N) = evalMatrix t M * evalMatrix t N := by
  ext i j
  change coefficient t (codeSum (List.ofFn (fun k => mulCode (M i k) (N k j)))) =
    ∑ k, coefficient t (M i k) * coefficient t (N k j)
  rw [coefficient_sum, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun k _ => coefficient_mul t ht _ _

theorem eval_mulVec (t : F) (ht : t ^ 4 = t + 1)
    (M : Matrix (Fin 16) (Fin 16) (Fin 16)) (x : Fin 16 → Fin 16) :
    evalVector t (codeMulVec M x) = (evalMatrix t M).mulVec (evalVector t x) := by
  funext i
  change coefficient t (codeSum (List.ofFn (fun k => mulCode (M i k) (x k)))) =
    ∑ k, coefficient t (M i k) * coefficient t (x k)
  rw [coefficient_sum, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun k _ => coefficient_mul t ht _ _

theorem eval_vecMul (t : F) (ht : t ^ 4 = t + 1)
    (x : Fin 16 → Fin 16) (M : Matrix (Fin 16) (Fin 16) (Fin 16)) :
    evalVector t (codeVecMul x M) = Matrix.vecMul (evalVector t x) (evalMatrix t M) := by
  funext j
  change coefficient t (codeSum (List.ofFn (fun k => mulCode (x k) (M k j)))) =
    ∑ k, coefficient t (x k) * coefficient t (M k j)
  rw [coefficient_sum, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun k _ => coefficient_mul t ht _ _

@[expose] def codeOne : Matrix (Fin 16) (Fin 16) (Fin 16) := fun i j => if i = j then 1 else 0

@[expose] def codeAdd (M N : Matrix (Fin 16) (Fin 16) (Fin 16)) :
    Matrix (Fin 16) (Fin 16) (Fin 16) := fun i j => addCode (M i j) (N i j)

@[expose] def codeOuter (x y : Fin 16 → Fin 16) : Matrix (Fin 16) (Fin 16) (Fin 16) :=
  fun i j => mulCode (x i) (y j)

omit [CharP F 2] in
theorem eval_one (t : F) : evalMatrix t codeOne = 1 := by
  ext i j
  change coefficient t (if i = j then 1 else 0) = if i = j then 1 else 0
  split_ifs <;> rfl

theorem eval_add (t : F) (M N : Matrix (Fin 16) (Fin 16) (Fin 16)) :
    evalMatrix t (codeAdd M N) = evalMatrix t M + evalMatrix t N := by
  ext i j
  exact coefficient_add t _ _

theorem eval_outer (t : F) (ht : t ^ 4 = t + 1) (x y : Fin 16 → Fin 16) :
    evalMatrix t (codeOuter x y) = Matrix.vecMulVec (evalVector t x) (evalVector t y) := by
  ext i j
  exact coefficient_mul t ht _ _

/-- A finite Boolean check, reduced by the kernel in the certificate modules. -/
@[expose] def checkMatrix (M N : Matrix (Fin 16) (Fin 16) (Fin 16)) : Bool :=
  (List.finRange 16).all (fun i => (List.finRange 16).all
    (fun j => (M i j).val == (N i j).val))

theorem checkMatrix_sound (M N : Matrix (Fin 16) (Fin 16) (Fin 16))
    (h : checkMatrix M N = true) : M = N := by
  funext i j
  apply Fin.ext
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j))

@[expose] def checkVector (x y : Fin 16 → Fin 16) : Bool :=
  (List.finRange 16).all (fun i => (x i).val == (y i).val)

theorem checkVector_sound (x y : Fin 16 → Fin 16)
    (h : checkVector x y = true) : x = y := by
  funext i
  apply Fin.ext
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density
