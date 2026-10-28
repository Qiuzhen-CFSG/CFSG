module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.USquare.Arithmetic

/-!
# Exact row selection for one-bit U product inputs

A checked power-of-two hint skips accumulation and selects its widened input
row. The general branch uses the already proved shortened accumulator. Both
branches equal the literal published row checker for every hint.
Source: ATLAS M24G1-P1; see CubeProducts/source/README.md.
-/

@[expose] public section
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.UProducts
open Arithmetic

theorem accum_single (k : Nat) (xs : List Nat) : accum (2^k) xs = xs[k]! := by
  induction xs generalizing k with
  | nil => simp [accum]
  | cons x xs ih =>
    cases k with
    | zero => simp [accum, accum_zero]
    | succ k =>
      simp only [pow_succ', accum, Nat.mul_mod_right, Nat.zero_mul, Nat.zero_add]
      rw [Nat.mul_comm 2, Nat.mul_div_left _ (by decide), ih]
      rfl

private theorem wide_lengths : ∀ r ∈ Inputs.uWide, r.length = 32 := by
  decide +kernel

theorem shortChunks_single (k : Nat) :
    shortChunks (2^k) Inputs.uWide = GeneratorOrders.getRow 32 Inputs.uWide k := by
  rw [shortChunks_eq, accumChunks_eq, accum_single,
    GeneratorOrders.getRow_eq 32 (by decide) Inputs.uWide wide_lengths]

def hintedRow (a hint : Nat) : Nat :=
  if a == 2^hint then
    GeneratorOrders.compressTree 6 1792 (GeneratorOrders.getRow 32 Inputs.uWide hint)
  else row a

theorem hintedRow_eq (a hint : Nat) : hintedRow a hint = row a := by
  unfold hintedRow
  split
  · next h =>
    have ha : a = 2^hint := by simpa only [beq_iff_eq] using h
    rw [ha, row, shortChunks_single]
  · rfl

def hintedBlock : List Nat → List Nat → List Nat
  | [], _ => []
  | a::as, hs => hintedRow a hs.head! :: hintedBlock as hs.tail

theorem hintedBlock_eq (as hs : List Nat) : hintedBlock as hs = as.map row := by
  induction as generalizing hs with
  | nil => rfl
  | cons a as ih => simp only [hintedBlock, List.map_cons, hintedRow_eq, ih]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.UProducts
