module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixData

/-!
# Entrywise certification of the cubic matrix witness

A 27-term dot product certifies each matrix entry. The finite decision
procedure is reduced by the kernel; no native evaluation is used.

Source: the literal ATLAS degree-27 matrices over GF(7) retained in
`CubicExtension/source/`. Generated witnesses are checked by Lean, independently
of the Python generator; see `MatrixWitness/source/README.md`.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness

open MatrixData

abbrev Mat := Matrix (Fin 27) (Fin 27) (ZMod 7)

def ProductEntries (a b c : Mat) : Prop :=
  ∀ i j, a i 0 * b 0 j +
    a i 1 * b 1 j +
    a i 2 * b 2 j +
    a i 3 * b 3 j +
    a i 4 * b 4 j +
    a i 5 * b 5 j +
    a i 6 * b 6 j +
    a i 7 * b 7 j +
    a i 8 * b 8 j +
    a i 9 * b 9 j +
    a i 10 * b 10 j +
    a i 11 * b 11 j +
    a i 12 * b 12 j +
    a i 13 * b 13 j +
    a i 14 * b 14 j +
    a i 15 * b 15 j +
    a i 16 * b 16 j +
    a i 17 * b 17 j +
    a i 18 * b 18 j +
    a i 19 * b 19 j +
    a i 20 * b 20 j +
    a i 21 * b 21 j +
    a i 22 * b 22 j +
    a i 23 * b 23 j +
    a i 24 * b 24 j +
    a i 25 * b 25 j +
    a i 26 * b 26 j = c i j

instance (a b c : Mat) : Decidable (ProductEntries a b c) :=
  @Nat.decidableForallFin 27 _ (fun _i =>
    @Nat.decidableForallFin 27 _ (fun _j => inferInstance))

theorem mul_of_entries (a b c : Mat) (h : ProductEntries a b c) : a * b = c := by
  ext i j
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, Fin.succ, add_assoc] using h i j

/-- The cubic scalar whose nontriviality detects the central kernel. -/
def scalarMatrix : Mat := Matrix.scalar (Fin 27) (2 : ZMod 7)

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
