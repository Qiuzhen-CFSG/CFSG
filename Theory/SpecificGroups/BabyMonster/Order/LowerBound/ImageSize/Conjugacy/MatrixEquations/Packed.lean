module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.Data.Matrix.Basic

/-!
# Multiplication certificates for blocked binary rows

The Baby Monster data store rows in arrays of blocks of 64. This adapter uses
the XOR soundness lemma of the Thompson checker, without flattening those
literal blocks. Bit `j` is column `j`; selecting rows therefore computes the
ordinary matrix product with the same right-conjugation convention.

The product and identity criteria are stated for an arbitrary dimension to
keep elaboration from expanding concrete finite sums. In a finite matrix
monoid a right inverse is also a left inverse, so just one inverse product
needs a numerical certificate. Concrete data and their provenance are in
`Conjugacy/source/README.md`.
-/

open scoped BigOperators
namespace BabyMonster.OrderLowerBound.ConjugacyCertificate
open Thompson.BinaryMatrix

@[expose] public def row (b : Array (Array Nat)) (k : Nat) : Nat := (b[k / 64]!)[k % 64]!
@[expose] public def product (a : Nat) (b : Array (Array Nat)) : Nat → Nat
  | 0 => 0
  | k+1 => product a b k ^^^ (if a.testBit k then row b k else 0)

public theorem bit_product (a : Nat) (b : Array (Array Nat)) (n j : Nat) :
    bit (product a b n) j = ∑ k ∈ Finset.range n, bit a k * bit (row b k) j := by
  induction n with
  | zero => simp [product, bit]
  | succ n ih =>
    rw [product, bit_xor, ih, Finset.sum_range_succ]
    congr 1
    cases h : a.testBit n <;> simp [bit, h]

@[expose] public def decode (n : Nat) (b : Array (Array Nat)) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => bit (row b i.val) j.val

public theorem decode_mul_eq (n : Nat) (a b c d : Array (Array Nat))
    (h : ∀ i : Fin n, product (row a i.val) b n = product (row c i.val) d n) :
    decode n a * decode n b = decode n c * decode n d := by
  ext i j
  change (∑ k : Fin n, bit (row a i.val) k.val * bit (row b k.val) j.val) =
    ∑ k : Fin n, bit (row c i.val) k.val * bit (row d k.val) j.val
  rw [Fin.sum_univ_eq_sum_range (fun k => bit (row a i.val) k * bit (row b k) j.val),
    Fin.sum_univ_eq_sum_range (fun k => bit (row c i.val) k * bit (row d k) j.val), ← bit_product,
    ← bit_product, h i]

public theorem decode_mul_one (n : Nat) (a b : Array (Array Nat))
    (h : ∀ i : Fin n, product (row a i.val) b n = 2 ^ i.val) :
    decode n a * decode n b = 1 := by
  ext i j
  change (∑ k : Fin n, bit (row a i.val) k.val * bit (row b k.val) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => bit (row a i.val) k * bit (row b k) j.val), ← bit_product, h i]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

public theorem matrix_reverse_inverse (n : Nat) (a b : Matrix (Fin n) (Fin n) (ZMod 2))
    (h : a * b = 1) : b * a = 1 := mul_eq_one_comm.mp h

end BabyMonster.OrderLowerBound.ConjugacyCertificate
