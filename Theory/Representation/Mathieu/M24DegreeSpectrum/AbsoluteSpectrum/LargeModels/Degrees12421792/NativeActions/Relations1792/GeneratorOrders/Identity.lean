module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.LiteralProducts

/-!
# Blocked rows of the identity matrix

The finite-product decomposition of List.ofFn identifies the 56 blocks of 32
rows with the literal identity matrix used by the order certificates.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792

def identityBlock (b : Nat) : List Nat :=
  List.ofFn (fun i : Fin 32 => 2^(b*32+i.val))

def identityChunks : List (List Nat) := List.ofFn (fun i : Fin 56 => identityBlock i.val)

theorem identityChunks_eq : identityChunks.flatten = identityRows 1792 := by
  change _ = List.ofFn (fun i : Fin (56*32) => 2^i.val)
  rw [List.ofFn_mul]
  rfl

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders
