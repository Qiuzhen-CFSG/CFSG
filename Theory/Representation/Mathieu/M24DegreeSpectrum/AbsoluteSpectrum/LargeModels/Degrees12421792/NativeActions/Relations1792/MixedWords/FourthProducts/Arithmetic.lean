module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
/-!
# Bounded arithmetic for the terminal fourth-power products

The four-bit expansion lookup is checked against the existing base-2048
expansion. Fixed-width accumulation avoids recomputing each block's length;
its equality with the general checker is proved from the block lengths.
`product` connects these computations to full matrix multiplication.

The concrete consumers are the five literal product adapters in the parent
module. Source: ATLAS M24G1-P1, as recorded in `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

theorem expand_mod (n a : Nat) : expand n (a % 2^n) = expand n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [expand, pow_succ', Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ih]

def nibbleCode : Nat := (nat_lit 0x200400801002004008000020040000100200400000002000008010020000080000200000001002000000000000040080100000400800000004000010000040000000000000801000000008000000000000100000000000)
def expandNibble (a : Nat) : Nat := nibbleCode / (nat_lit 0x100000000000)^(a%16) % (nat_lit 0x100000000000)

set_option maxRecDepth 8192 in
theorem expandNibble_small : ∀ a : Fin 16, expandNibble a = expand 4 a := by decide +kernel

theorem expandNibble_eq (a : Nat) : expandNibble a = expand 4 a := by
  have h := expandNibble_small ⟨a%16, Nat.mod_lt _ (by decide)⟩
  change expandNibble (a%16) = expand 4 (a%16) at h
  simpa only [expandNibble, Nat.mod_mod, show 16 = 2^4 from rfl, expand_mod] using h

def expandFast : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, a => expandNibble a + (nat_lit 0x100000000000) * expandFast k (a/16)

theorem expandFast_eq (k a : Nat) : expandFast k a = expand (4*k) a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [expandFast, expandNibble_eq, ih, Nat.mul_succ, Nat.add_comm (4*k) 4, expand_add]
    rfl

/-- Bounded outer traversal: eight nibbles per original 32-bit block. -/
def expandFastBlocks : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, a => expandFast 8 a + (nat_lit 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) *
      expandFastBlocks k (a/4294967296)

theorem expandFastBlocks_eq (k a : Nat) : expandFastBlocks k a = expand (32*k) a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [expandFastBlocks, expandFast_eq, ih, Nat.mul_succ 32 k,
      Nat.add_comm (32*k) 32, expand_add]
    rfl

/-- The faster blocked computation proves the original complete expansion bridge. -/
theorem expand_rows (xs ys : List Nat)
    (h : xs = ys.map (expandFastBlocks 56)) : xs = ys.map (expandFast 448) := by
  have he : expandFastBlocks 56 = expandFast 448 := by
    funext a
    rw [expandFastBlocks_eq, expandFast_eq]
  simpa only [he] using h

def accum32 : Nat → List (List Nat) → Nat
  | _, [] => 0
  | a,b::bs => accum a b + accum32 (a/4294967296) bs

theorem accum32_eq (a : Nat) (ws : List (List Nat)) (h : ∀ b ∈ ws, b.length = 32) :
    accum32 a ws = accumChunks a ws := by
  induction ws generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have ht : ∀ q ∈ bs, q.length = 32 := fun q hq => h q (by simp [hq])
    simp only [accum32, accumChunks, h b (by simp), ih _ ht]
    rfl

def row (a : Nat) (ws : List (List Nat)) : Nat := compressBlocks 32 56 (accum32 a ws)

theorem product (xs ys zs : List Nat) (ws : List (List Nat))
    (hx : xs.length = 1792) (hy : ys.length = 1792)
    (hw : ws.flatten = ys.map (expandFast 448))
    (hg : ∀ b ∈ ws, b.length = 32)
    (hc : xs.map (fun a => row a ws) = zs) :
    decodeRows 1792 xs * decodeRows 1792 ys = decodeRows 1792 zs := by
  have he : expandFast 448 = expandBlocks 32 56 := by
    funext a
    rw [expandFast_eq, expandBlocks_eq]
  apply product_chunks 32 56 (by decide) xs ys zs ws hx hy (by simpa only [he] using hw)
  have he' (a : Nat) : row a ws = compressBlocks 32 56 (accumChunks a ws) := by
    rw [row, accum32_eq a ws hg]
  simpa only [he'] using hc

/-- A single checked numerical row gives the corresponding actual matrix row. -/
theorem matrix_row (xs ys : List Nat) (ws : List (List Nat))
    (hx : xs.length = 1792) (hy : ys.length = 1792)
    (hw : ws.flatten = ys.map (expandFast 448))
    (hg : ∀ b ∈ ws, b.length = 32) (i j : Fin 1792) :
    (decodeRows 1792 xs * decodeRows 1792 ys) i j =
      Thompson.BinaryMatrix.bit (row xs[i.val]! ws) j.val := by
  have hp := product xs ys (xs.map (fun a => row a ws)) ws hx hy hw hg rfl
  have hi : i.val < xs.length := by simpa only [hx] using i.isLt
  have h := congrArg (fun m : Matrix (Fin 1792) (Fin 1792) (ZMod 2) => m i j) hp
  simpa [decodeRows, hi] using h

theorem flatten_map {α β : Type*} (f : α → β) (as : List (List α)) (bs : List (List β))
    (h : List.Forall₂ (fun a b => a.map f = b) as bs) : as.flatten.map f = bs.flatten := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.flatten_cons, List.map_append, hab, ih]

theorem decode_identity (n : Nat) : decodeRows n ((List.range n).map (fun i => 2^i)) = 1 := by
  ext i j
  simp [decodeRows, Thompson.BinaryMatrix.bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic
