module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

/-!
# Skipping zero chunks in the fixed matrix-row checker

A zero 32-bit coefficient chunk contributes no selected rows, because each
right-hand block has length 32. A zero base-2048 chunk contributes no output
bits during compression. The two optimizations are proved equal to the original
accumulator and compression, so `row_eq` preserves the existing checker exactly.

The concrete consumers are the complete Z-square and Z-cube block certificates.
Source: ATLAS M24G1-P1; see `source/README.md` for data and measurements.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.ZProducts.RowArithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic

private theorem accum_zero (bs : List Nat) : accum 0 bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [accum, Nat.zero_mod, Nat.zero_mul, Nat.zero_div, ih, Nat.zero_add]

private theorem accum_mod (a : Nat) (bs : List Nat) :
    accum (a % 2^bs.length) bs = accum a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, pow_succ', accum, Nat.mod_mul_right_mod,
      Nat.mod_mul_right_div_self, ih]

def accumSkip : Nat → List (List Nat) → Nat
  | _, [] => 0
  | a, b :: bs => (if a % 4294967296 = 0 then 0 else accum a b) +
      accumSkip (a / 4294967296) bs

private theorem accumSkip_eq (a : Nat) (bs : List (List Nat))
    (hl : ∀ b ∈ bs, b.length = 32) : accumSkip a bs = Arithmetic.accum32 a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.length = 32 := hl b (by simp)
    have ht : ∀ c ∈ bs, c.length = 32 := fun c hc => hl c (by simp [hc])
    have hh : (if a % 4294967296 = 0 then 0 else accum a b) = accum a b := by
      split
      · next hz =>
        rw [← accum_mod a b, hb]
        change 0 = accum (a % 4294967296) b
        rw [hz, accum_zero]
      · rfl
    simp only [accumSkip, Arithmetic.accum32, hh, ih _ ht]

private theorem compress_mul_pow (n a : Nat) : compress n (a * 2048^n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ← Nat.mul_assoc]
    simp [compress, Nat.mul_mod, ih]

private theorem compress_zero_low (a : Nat) (h : a % 2048^32 = 0) : compress 32 a = 0 := by
  have ha : a = (a / 2048^32) * 2048^32 := by
    have hd := Nat.mod_add_div a (2048^32)
    rw [h, Nat.zero_add] at hd
    exact hd.symm.trans (Nat.mul_comm _ _)
  rw [ha, compress_mul_pow]

def compressSkip : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, a => (if a % 2048^32 = 0 then 0 else compress 32 a) +
      2^32 * compressSkip n (a / 2048^32)

private theorem compressSkip_eq (n a : Nat) : compressSkip n a = compressBlocks 32 n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have hh : (if a % 2048^32 = 0 then 0 else compress 32 a) = compress 32 a := by
      split
      · next hz => exact (compress_zero_low a hz).symm
      · rfl
    simp only [compressSkip, compressBlocks, hh, ih]

def row (a : Nat) (bs : List (List Nat)) : Nat := compressSkip 56 (accumSkip a bs)

theorem row_eq (a : Nat) (bs : List (List Nat)) (hl : ∀ b ∈ bs, b.length = 32) :
    row a bs = Arithmetic.row a bs := by
  unfold row Arithmetic.row
  rw [compressSkip_eq, accumSkip_eq a bs hl]

/-- Transport a whole certificate without reducing its concrete rows. -/
theorem map_eq (xs : List Nat) (bs : List (List Nat)) (hl : ∀ b ∈ bs, b.length = 32) :
    xs.map (fun a => row a bs) = xs.map (fun a => Arithmetic.row a bs) := by
  exact congrArg (fun f : Nat → Nat => xs.map f) (funext (fun a => row_eq a bs hl))

/-- Apply a closed optimized check at a symbolic, noncomputing boundary. -/
theorem of_rows (xs zs : List Nat) (bs : List (List Nat))
    (hl : ∀ b ∈ bs, b.length = 32)
    (h : xs.map (fun a => row a bs) = zs) :
    xs.map (fun a => Arithmetic.row a bs) = zs :=
  (map_eq xs bs hl).symm.trans h

private theorem map_join (f : Nat → Nat) (xs ys : List Nat)
    (h : (xs.take 8).map f = ys.take 8)
    (ht : (xs.drop 8).map f = ys.drop 8) : xs.map f = ys := by
  conv_lhs => rw [← List.take_append_drop 8 xs]
  rw [List.map_append, h, ht, List.take_append_drop]

/-- Four consecutive checked chunks cover the original row block exactly. -/
theorem of_chunks (xs zs : List Nat) (bs : List (List Nat))
    (hl : ∀ b ∈ bs, b.length = 32)
    (h0 : (xs.take 8).map (fun a => row a bs) = zs.take 8)
    (h1 : ((xs.drop 8).take 8).map (fun a => row a bs) = (zs.drop 8).take 8)
    (h2 : ((xs.drop 16).take 8).map (fun a => row a bs) = (zs.drop 16).take 8)
    (h3 : (xs.drop 24).map (fun a => row a bs) = zs.drop 24) :
    xs.map (fun a => Arithmetic.row a bs) = zs := by
  have h16 := map_join (fun a => row a bs) (xs.drop 16) (zs.drop 16) h2
    (by simpa only [List.drop_drop] using h3)
  have h8 := map_join (fun a => row a bs) (xs.drop 8) (zs.drop 8) h1
    (by simpa only [List.drop_drop] using h16)
  exact of_rows xs zs bs hl (map_join (fun a => row a bs) xs zs h0 h8)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.ZProducts.RowArithmetic
