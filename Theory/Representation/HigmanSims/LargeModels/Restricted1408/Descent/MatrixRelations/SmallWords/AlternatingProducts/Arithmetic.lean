module

public import Theory.LinearAlgebra.PackedBinaryRows
public import Mathlib.Data.List.Forall2

/-!
# Checked four-bit lookup certificates for the alternating HS words

Each lookup table contains all sixteen XOR combinations of four original rows.
`GoodTable` checks these combinations, and `tableProduct_sound` proves that
scanning the tables computes the original packed row product. Complete row
checks are then exported to the unchanged `SmallWordProducts.mul_of_rows`.
See `../source/README.md` for the literal ATLAS words and data attribution.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts.AlternatingCertificate
open PackedBinaryRows
lemma listProduct_append (x s : Nat) (rs ts : List Nat) :
    listProduct x s (rs ++ ts) =
      listProduct x s rs ^^^ listProduct x (s + rs.length) ts := by
  induction rs generalizing s with
  | nil => simp [listProduct]
  | cons r rs ih =>
    simp only [List.cons_append, listProduct, ih, List.length_cons]
    rw [Nat.xor_assoc]
    rw [show s + 1 + rs.length = s + (rs.length + 1) by omega]

lemma listProduct_shift (x s t : Nat) (rs : List Nat) :
    listProduct x (s + t) rs = listProduct (x >>> s) t rs := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih =>
    simp only [listProduct, Nat.testBit_shiftRight]
    rw [Nat.add_assoc, ih]

lemma listProduct_congr_bits (x y s t : Nat) (rs : List Nat)
    (h : ∀ i, i < rs.length → x.testBit (s+i) = y.testBit (t+i)) :
    listProduct x s rs = listProduct y t rs := by
  induction rs generalizing s t with
  | nil => rfl
  | cons r rs ih =>
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero] at h0
    rw [listProduct, listProduct, h0, ih]
    intro i hi
    have h1 := h (i+1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1] using h1

lemma listProduct_mod (x k : Nat) (rs : List Nat) (hs : rs.length = k) :
    listProduct (x % 2^k) 0 rs = listProduct x 0 rs := by
  apply listProduct_congr_bits
  intro i hi
  have hik : i < k := hs ▸ hi
  simp [Nat.testBit_mod_two_pow, hik]

/-- Extract a packed lookup entry. -/
def lookup (t v : Nat) : Nat := t / 2 ^ (v * 1408) % 2 ^ 1408

/-- XOR the precomputed four-bit combination for each consecutive block. -/
def tableProduct (x : Nat) : List Nat → Nat
  | [] => 0
  | t :: ts => lookup t (x % 16) ^^^ tableProduct (x / 16) ts

def GoodTable (rs : List Nat) (t : Nat) : Prop :=
  rs.length = 4 ∧ ∀ v : Fin 16, lookup t v.val = listProduct v.val 0 rs

instance (rs : List Nat) (t : Nat) : Decidable (GoodTable rs t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem tableProduct_sound (rows : List (List Nat)) (tables : List Nat)
    (h : List.Forall₂ GoodTable rows tables) (x : Nat) :
    tableProduct x tables = listProduct x 0 rows.flatten := by
  induction h generalizing x with
  | nil => rfl
  | @cons rs t rows tables h ht ih =>
    rw [tableProduct, List.flatten_cons, listProduct_append]
    rw [h.2 ⟨x % 16, Nat.mod_lt _ (by decide)⟩, listProduct_mod x 4 rs h.1, ih]
    rw [Nat.zero_add, h.1]
    congr 1
    simpa only [Nat.add_zero, Nat.shiftRight_eq_div_pow] using
      (listProduct_shift x 4 0 rows.flatten).symm

def checkProducts (ts : List Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, z :: zs => (tableProduct x ts == z) && checkProducts ts xs zs
  | _, _ => false

theorem checkProducts_sound (ts xs zs : List Nat) (h : checkProducts ts xs zs = true)
    (i : Nat) (hi : i < xs.length) : tableProduct xs[i]! ts = zs[i]! := by
  induction xs generalizing zs i with
  | nil => simp at hi
  | cons x xs ih =>
    cases zs with
    | nil => simp [checkProducts] at h
    | cons z zs =>
      simp only [checkProducts, Bool.and_eq_true, beq_iff_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ i =>
        simpa using ih zs h.2 i (by simpa using hi)

theorem rows_of_checks (x y z : Array Nat) (rows : List (List Nat)) (ts : List Nat)
    (hx : x.size = 1408) (hr : rows.flatten = y.toList)
    (ht : List.Forall₂ GoodTable rows ts)
    (hc : checkProducts ts x.toList z.toList = true) (i : Fin 1408) :
    listProduct x[i.val]! 0 y.toList = z[i.val]! := by
  rw [← hr, ← tableProduct_sound rows ts ht]
  simpa only [Array.getElem!_toList] using
    checkProducts_sound ts x.toList z.toList hc i.val (by simp [hx])

def oneRows : Array Nat := Array.ofFn (fun i : Fin 1408 => 2 ^ i.val)

theorem oneRows_get (i : Fin 1408) : oneRows[i.val]! = 2 ^ i.val := by
  simp [oneRows, i.isLt]

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts.AlternatingCertificate
