module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.Data
/-!
# Packed arithmetic for the Fi22 action certificate

Six base-four digits represent six elements of the published quadratic field.
Bit operations compute six products simultaneously; parity computes their sum.
The proofs reduce the two coefficients in each digit to Boolean identities,
then identify the packed transvection with the original quadratic-field formula.
This avoids repeating field-instance reduction in every action-table entry.

Application and source: the literal root action in GLS3 Table 5.3t,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, with ATLAS F22G1-p3510B0 coordinates.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Labeling.ActionTable.Arithmetic

def ofBits (a b : Bool) : Four := ⟨if a then 1 else 0, if b then 1 else 0⟩

theorem digit_mod (n : Nat) : digit (n % 4) = digit n := by
  unfold digit
  congr 1
  · congr 1
    omega
  · congr 1
    omega

theorem digit_bits (n : Nat) : digit n = ofBits (n.testBit 0) (n.testBit 1) := by
  have h : ∀ n : Fin 4, digit n.val = ofBits (n.val.testBit 0) (n.val.testBit 1) := by
    decide +kernel
  have hn := h ⟨n % 4, Nat.mod_lt _ (by decide)⟩
  rw [digit_mod] at hn
  simpa only [show 4 = 2^2 from rfl, Nat.testBit_mod_two_pow, show decide (0 < 2) = true from rfl,
    show decide (1 < 2) = true from rfl, Bool.true_and] using hn

theorem vector_bits (n : Nat) (k : Fin 6) :
    vector n k = ofBits (n.testBit (2*k.val)) (n.testBit (2*k.val+1)) := by
  unfold vector
  rw [digit_mod]
  simp only [digit_bits, Nat.testBit_shiftRight, Nat.add_zero]

def mul (x y : Nat) : Nat :=
  let a := x &&& 1365
  let b := (x >>> 1) &&& 1365
  let c := y &&& 1365
  let d := (y >>> 1) &&& 1365
  ((a &&& c) ^^^ (b &&& d)) ||| (((a &&& d) ^^^ (b &&& c) ^^^ (b &&& d)) <<< 1)
def square (x : Nat) : Nat := x ^^^ ((x >>> 1) &&& 1365)
def sum (x : Nat) : Nat :=
  (x ^^^ (x >>> 2) ^^^ (x >>> 4) ^^^ (x >>> 6) ^^^ (x >>> 8) ^^^ (x >>> 10)) % 4

theorem bits_mul (a b c d : Bool) :
    ofBits ((a && c) ^^ (b && d)) (((a && d) ^^ (b && c)) ^^ (b && d)) =
      ofBits a b * ofBits c d := by
  revert a b c d
  decide +kernel

theorem vector_mul (x y : Nat) : vector (mul x y) = vector x * vector y := by
  funext k
  simp only [Pi.mul_apply, vector_bits]
  fin_cases k <;>
    simp only [mul, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight] <;>
    norm_num only [Nat.testBit_eq_decide_div_mod_eq] <;>
    simp only [decide_true, decide_false, Bool.and_true, Bool.and_false, Bool.false_and,
      Bool.true_and, Bool.xor_false, Bool.or_false, Bool.false_or] <;>
    exact bits_mul _ _ _ _

theorem bits_square (a b : Bool) : ofBits (a ^^ b) b = (ofBits a b)^2 := by
  revert a b
  decide +kernel

theorem vector_square (x : Nat) : vector (square x) = fun k => (vector x k)^2 := by
  funext k
  simp only [vector_bits]
  fin_cases k <;>
    simp only [square, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight] <;>
    norm_num only [Nat.testBit_eq_decide_div_mod_eq] <;>
    simp only [decide_true, decide_false, Bool.and_true, Bool.and_false, Bool.xor_false] <;>
    exact bits_square _ _

theorem bits_add (a b c d : Bool) :
    ofBits (a ^^ c) (b ^^ d) = ofBits a b + ofBits c d := by
  revert a b c d
  decide +kernel

theorem digit_xor (x y : Nat) : digit (x ^^^ y) = digit x + digit y := by
  simp only [digit_bits, Nat.testBit_xor]
  exact bits_add _ _ _ _

theorem vector_xor (x y : Nat) : vector (x ^^^ y) = vector x + vector y := by
  funext k
  simp only [vector_bits, Nat.testBit_xor, Pi.add_apply]
  exact bits_add _ _ _ _

theorem digit_sum (x : Nat) : digit (sum x) = ∑ k : Fin 6, vector x k := by
  simp only [sum, digit_mod, digit_xor, vector, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.mul_zero, Nat.shiftRight_zero,
    Nat.reduceMul, Nat.reduceAdd]
  ac_rfl

theorem vector_replicate (s : Fin 4) : vector (s.val * 1365) = fun _ => digit s.val := by
  revert s
  decide +kernel

def trans (x y : Nat) : Nat := y ^^^ mul ((sum (mul (square x) y)) * 1365) x

theorem vector_trans (x y : Nat) : vector (trans x y) = transvection (vector x) (vector y) := by
  rw [trans, vector_xor, vector_mul,
    vector_replicate ⟨sum (mul (square x) y), Nat.mod_lt _ (by decide)⟩]
  simp only [digit_sum, vector_mul, vector_square, Pi.mul_apply, transvection,
    Pi.smul_def, smul_eq_mul]
  rfl

end Sporadic.Fischer.Fi22.TransvectionComparison.Labeling.ActionTable.Arithmetic
