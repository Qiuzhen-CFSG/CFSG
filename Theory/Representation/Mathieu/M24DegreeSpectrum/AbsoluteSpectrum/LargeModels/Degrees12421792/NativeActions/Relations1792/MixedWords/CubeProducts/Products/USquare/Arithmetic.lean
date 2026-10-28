module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Inputs.U
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders.Checker

/-!
# Shortened accumulation for the two U products

Stop accumulating once the left row has no bits left. The result equals
the published checker exactly; balanced compression then uses its existing proof.
Source: ATLAS M24G1-P1; see CubeProducts/source/README.md.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.UProducts
open Arithmetic Inputs

theorem accum_zero (xs : List Nat) : accum 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [accum, ih]

theorem accumChunks_zero (xs : List (List Nat)) : accumChunks 0 xs = 0 := by
  rw [accumChunks_eq, accum_zero]

def shortAccum : Nat → List Nat → Nat
  | _, [] => 0
  | a, b::bs => if a == 0 then 0 else (a % 2) * b + shortAccum (a / 2) bs

theorem shortAccum_eq (a : Nat) (xs : List Nat) : shortAccum a xs = accum a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    by_cases ha : a = 0
    · subst a; simp [shortAccum, accum_zero]
    · simp [shortAccum, ha, accum, ih]

def shortChunks : Nat → List (List Nat) → Nat
  | _, [] => 0
  | a, b::bs => if a == 0 then 0 else
      shortAccum a b + shortChunks (a / 2 ^ b.length) bs

theorem shortChunks_eq (a : Nat) (xs : List (List Nat)) :
    shortChunks a xs = accumChunks a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    by_cases ha : a = 0
    · subst a; simp [shortChunks, accumChunks_zero]
    · simp [shortChunks, ha, accumChunks, shortAccum_eq, ih]

def row (a : Nat) : Nat := GeneratorOrders.compressTree 6 1792 (shortChunks a uWide)

theorem row_eq : row = (fun a => compressBlocks 32 56 (accumChunks a uWide)) := by
  funext a
  simp only [row, GeneratorOrders.compressTree_eq, shortChunks_eq, compressBlocks_eq]


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.UProducts
