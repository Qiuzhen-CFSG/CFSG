module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic

/-!
# Complete block assembly for the mixed cube certificates

The row certificates cover every block of the published tables. `map_flatten`
combines them without dropping rows. The identity blocks decode to the literal
matrix identity in the original row convention. These helpers are consumed by
all five products in `CubeProducts`.

Source: ATLAS M24G1-P1; see `source/README.md` and `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
open Arithmetic

def identityBlock (b : Nat) : List Nat :=
  (List.range 32).map fun k => 2 ^ (32 * b + k)

def identityBlocks : List (List Nat) := (List.range 56).map identityBlock

set_option maxRecDepth 8192 in
theorem identity_flatten : identityBlocks.flatten =
    List.ofFn (fun i : Fin 1792 => 2 ^ i.val) := by
  decide +kernel

theorem decode_identity (n : Nat) :
    decodeRows n (List.ofFn (fun i : Fin n => 2 ^ i.val)) = 1 := by
  ext i j
  simp [decodeRows, Thompson.BinaryMatrix.bit,
    Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem identity_decode : decodeRows 1792 identityBlocks.flatten = 1 := by
  rw [identity_flatten]
  exact decode_identity 1792

theorem map_flatten {α β : Type} (f : α → β) {xs : List (List α)}
    {ys : List (List β)} (h : List.Forall₂ (fun x y => x.map f = y) xs ys) :
    xs.flatten.map f = ys.flatten := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.flatten_cons, List.map_append, hab, ih]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
