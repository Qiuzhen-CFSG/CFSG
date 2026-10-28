module

public import Theory.LinearAlgebra.PackedBinaryRows
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# Division-based packed row products

Consuming the input integer one bit at a time avoids repeated large shifts
in kernel reduction. The comparison with `listProduct` proves this is the
same XOR computation used by the literal matrix decoder.
-/

@[expose] public section
namespace PackedBinaryRows

def fastProduct : Nat → List Nat → Nat
 | _, [] => 0
 | x, r::rs => Nat.xor (if x % 2 == 1 then r else 0) (fastProduct (x/2) rs)

lemma fastProduct_eq_listProduct (x start : Nat) (rs : List Nat) :
    fastProduct (x / 2^start) rs = listProduct x start rs := by
  induction rs generalizing start with
  | nil => rfl
  | cons r rs ih =>
    simp only [fastProduct, listProduct]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, ih]
    congr 1
    simp [Nat.testBit_eq_decide_div_mod_eq]

lemma fastProduct_eq (x : Nat) (rs : List Nat) :
    fastProduct x rs = listProduct x 0 rs := by
  simpa only [Nat.pow_zero, Nat.div_one] using fastProduct_eq_listProduct x 0 rs

end PackedBinaryRows
