module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders.Checker
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.LiteralProducts

/-!
# Matrix decoding and identity rows for the fourth-word certificates

The existing carry-free checker supplies the multiplication semantics.
The identity block decomposition is proved at the same 46-by-27 boundary.
Source: ATLAS M24G1-P1 and M24G1-f2r1242B0.m1/.m2.
See `source/README.md`; bit j of row i is entry (i,j), without transposition.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

theorem decodeRows_list (xs : List Nat) :
    decodeRows 1242 xs = Thompson.BinaryMatrix.decode 1242 xs.toArray := by
  simpa only [List.toList_toArray] using decodeRows_array 1242 xs.toArray

def identityBlock (b : Nat) : List Nat :=
  List.ofFn (fun i : Fin 27 => 2^(b*27+i.val))

def identityChunks : List (List Nat) := List.ofFn (fun i : Fin 46 => identityBlock i.val)

theorem identityChunks_eq : identityChunks.flatten = identityRows 1242 := by
  change _ = List.ofFn (fun i : Fin (46*27) => 2^i.val)
  rw [List.ofFn_mul]
  rfl

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts
