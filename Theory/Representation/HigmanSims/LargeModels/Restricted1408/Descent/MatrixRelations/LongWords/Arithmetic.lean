module

public import Theory.LinearAlgebra.PackedBinaryRows

/-!
# Packed simultaneous binary row products

Pack rows as base-2^w digits. The mask has a one in the lowest bit of each
row. At column k, masking the shifted left matrix selects these bits; their
product with a right row places that row in exactly the selected positions.
XOR adds the contributions. `Soundness` proves that no carries can cross row
boundaries and connects this calculation to ordinary matrix multiplication.

This checker uses only natural-number operations checked by Lean's kernel.
The HS application retains the multiplication order of ATLAS HSG1-P1.M.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.LongPacked

def pack (w : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + 2^w * pack w xs

def chunk (w i x : Nat) : Nat := x / 2^(w*i) % 2^w

def product (w x mask start : Nat) : List Nat → Nat
  | [] => 0
  | b :: bs => (((x >>> start) &&& mask) * b) ^^^ product w x mask (start+1) bs

/-- A certificate for the entire product; every input and output row is retained. -/
def ProductCertificate (a b c : Array Nat) : Prop :=
  product 1408 (pack 1408 a.toList) (pack 1408 (List.replicate 1408 1)) 0 b.toList =
    pack 1408 c.toList

def BoundedRows (a : Array Nat) : Prop :=
  a.toList.all (fun x => decide (x < 2^1408)) = true

def identityRows : Array Nat := ((List.range 1408).map (fun i => 2^i)).toArray

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.LongPacked
