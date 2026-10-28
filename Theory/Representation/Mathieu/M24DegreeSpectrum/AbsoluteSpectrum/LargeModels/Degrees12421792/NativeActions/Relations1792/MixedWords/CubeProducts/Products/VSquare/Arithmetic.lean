module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders.Checker
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Inputs.V

/-!
# Bounded row computations for the two fixed V products

Zero 32-bit masks contribute no row sum; a zero remaining mask ends
the traversal. The trimmed fixed-width accumulation and balanced compression are
proved equal to the original blocked arithmetic. Each numerical certificate
is thereby converted to the literal row equation required by `product_chunks`.
The input lengths are checked for the unchanged published V table.

Source: ATLAS M24G1-P1; see `../../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.VChecks
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

theorem lengths : ∀ b ∈ Inputs.vWide, b.length = 32 := by
  decide +kernel

theorem accum_zero (xs : List Nat) : accum 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [accum, ih]

theorem accum32_zero (xs : List (List Nat)) : accum32 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [accum32, accum_zero, ih]

theorem accum_mod (a : Nat) (xs : List Nat) :
    accum (a % 2 ^ xs.length) xs = accum a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, pow_succ', accum,
      Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ih]

def accumTrim : Nat → List (List Nat) → Nat
  | _, [] => 0
  | a, b :: bs => if a == 0 then 0 else
      (if a % 4294967296 == 0 then 0 else accum a b) + accumTrim (a / 4294967296) bs

theorem accumTrim_eq (a : Nat) (xs : List (List Nat))
    (hl : ∀ b ∈ xs, b.length = 32) : accumTrim a xs = accum32 a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.length = 32 := hl x (by simp)
    have ht : ∀ b ∈ xs, b.length = 32 := fun b hb => hl b (by simp [hb])
    simp only [accumTrim]
    split
    · next h =>
      have ha : a = 0 := by simpa only [beq_iff_eq] using h
      rw [ha, accum32_zero]
    · rw [ih _ ht]
      change (if a % 4294967296 == 0 then 0 else accum a x) +
        accum32 (a / 4294967296) xs = accum a x + accum32 (a / 4294967296) xs
      congr 1
      split
      · next h =>
        have ha : a % 4294967296 = 0 := by simpa only [beq_iff_eq] using h
        have he := accum_mod a x
        rw [hx, show 2 ^ 32 = 4294967296 from rfl, ha, accum_zero] at he
        exact he
      · rfl

def fastRow (a : Nat) : Nat := compressTree 6 1792 (accumTrim a Inputs.vWide)

theorem fastRow_eq (a : Nat) :
    fastRow a = compressBlocks 32 56 (accumChunks a Inputs.vWide) := by
  rw [fastRow, compressTree_eq, accumTrim_eq a Inputs.vWide lengths,
    accum32_eq a Inputs.vWide lengths, compressBlocks_eq]

theorem rows (xs ys : List Nat) (h : xs.map fastRow = ys) :
    xs.map (fun a => compressBlocks 32 56 (accumChunks a Inputs.vWide)) = ys := by
  have he : fastRow = fun a => compressBlocks 32 56 (accumChunks a Inputs.vWide) :=
    funext fastRow_eq
  simpa only [he] using h


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.VChecks
