module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.LiteralProducts

/-!
# The blocked identity in degree 1242

The finite-product formula for List.ofFn identifies 46 blocks of 27
rows with the existing identityRows definition.
Source: ATLAS M24G1-P1 and the untransposed M24G1-f2r1242B0 matrices.
See `CubeProducts/source/README.md` for conventions and validation.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.Identity

def block (b : Nat) : List Nat := List.ofFn (fun i : Fin 27 => 2^(b*27+i.val))

def rows : List Nat := (List.ofFn (fun i : Fin 46 => block i.val)).flatten

private theorem flatten_blocks (f : Nat → List Nat) :
    (List.ofFn (fun i : Fin 46 => f i.val)).flatten =
      f 0 ++ (f 1 ++ (f 2 ++ (f 3 ++ (f 4 ++ (f 5 ++ (f 6 ++ (f 7 ++ (f 8 ++ (f 9 ++ (f 10 ++ (f 11 ++ (f 12 ++ (f 13 ++ (f 14 ++ (f 15 ++ (f 16 ++ (f 17 ++ (f 18 ++ (f 19 ++ (f 20 ++ (f 21 ++ (f 22 ++ (f 23 ++ (f 24 ++ (f 25 ++ (f 26 ++ (f 27 ++ (f 28 ++ (f 29 ++ (f 30 ++ (f 31 ++ (f 32 ++ (f 33 ++ (f 34 ++ (f 35 ++ (f 36 ++ (f 37 ++ (f 38 ++ (f 39 ++ (f 40 ++ (f 41 ++ (f 42 ++ (f 43 ++ (f 44 ++ (f 45))))))))))))))))))))))))))))))))))))))))))))) := by
  change f 0 ++ (f 1 ++ (f 2 ++ (f 3 ++ (f 4 ++ (f 5 ++ (f 6 ++ (f 7 ++ (f 8 ++ (f 9 ++ (f 10 ++ (f 11 ++ (f 12 ++ (f 13 ++ (f 14 ++ (f 15 ++ (f 16 ++ (f 17 ++ (f 18 ++ (f 19 ++ (f 20 ++ (f 21 ++ (f 22 ++ (f 23 ++ (f 24 ++ (f 25 ++ (f 26 ++ (f 27 ++ (f 28 ++ (f 29 ++ (f 30 ++ (f 31 ++ (f 32 ++ (f 33 ++ (f 34 ++ (f 35 ++ (f 36 ++ (f 37 ++ (f 38 ++ (f 39 ++ (f 40 ++ (f 41 ++ (f 42 ++ (f 43 ++ (f 44 ++ (f 45 ++ (([] : List Nat))))))))))))))))))))))))))))))))))))))))))))))) = _
  simp only [List.append_nil]

theorem rows_blocks : rows = block 0 ++ (block 1 ++ (block 2 ++ (block 3 ++ (block 4 ++ (block 5 ++ (block 6 ++ (block 7 ++ (block 8 ++ (block 9 ++ (block 10 ++ (block 11 ++ (block 12 ++ (block 13 ++ (block 14 ++ (block 15 ++ (block 16 ++ (block 17 ++ (block 18 ++ (block 19 ++ (block 20 ++ (block 21 ++ (block 22 ++ (block 23 ++ (block 24 ++ (block 25 ++ (block 26 ++ (block 27 ++ (block 28 ++ (block 29 ++ (block 30 ++ (block 31 ++ (block 32 ++ (block 33 ++ (block 34 ++ (block 35 ++ (block 36 ++ (block 37 ++ (block 38 ++ (block 39 ++ (block 40 ++ (block 41 ++ (block 42 ++ (block 43 ++ (block 44 ++ (block 45))))))))))))))))))))))))))))))))))))))))))))) :=
  flatten_blocks block

theorem rows_eq : rows = identityRows 1242 := by
  change _ = List.ofFn (fun i : Fin (46*27) => 2^i.val)
  rw [List.ofFn_mul]
  rfl

theorem decode_rows : Thompson.BinaryMatrix.decode 1242 rows.toArray = 1 := by
  rw [rows_eq, decode_identityRows]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.Identity
