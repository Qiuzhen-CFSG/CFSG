module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixWitness.Certificate

/-!
# Natural-number dot-product certificates

Sum products of the canonical integer representatives, then reduce once
modulo seven. Casting the checked equality back to GF(7) proves the literal
matrix product. This avoids modular reduction at each intermediate sum.

Source: the literal ATLAS degree-27 matrices over GF(7) retained in
`CubicExtension/source/`. Generated witnesses are checked by Lean, independently
of the Python generator; see `MatrixWitness/source/README.md`.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness

def NatProductEntries (a b c : Mat) : Prop := ∀ i j,
  ((a i 0).val * (b 0 j).val +
    (a i 1).val * (b 1 j).val +
    (a i 2).val * (b 2 j).val +
    (a i 3).val * (b 3 j).val +
    (a i 4).val * (b 4 j).val +
    (a i 5).val * (b 5 j).val +
    (a i 6).val * (b 6 j).val +
    (a i 7).val * (b 7 j).val +
    (a i 8).val * (b 8 j).val +
    (a i 9).val * (b 9 j).val +
    (a i 10).val * (b 10 j).val +
    (a i 11).val * (b 11 j).val +
    (a i 12).val * (b 12 j).val +
    (a i 13).val * (b 13 j).val +
    (a i 14).val * (b 14 j).val +
    (a i 15).val * (b 15 j).val +
    (a i 16).val * (b 16 j).val +
    (a i 17).val * (b 17 j).val +
    (a i 18).val * (b 18 j).val +
    (a i 19).val * (b 19 j).val +
    (a i 20).val * (b 20 j).val +
    (a i 21).val * (b 21 j).val +
    (a i 22).val * (b 22 j).val +
    (a i 23).val * (b 23 j).val +
    (a i 24).val * (b 24 j).val +
    (a i 25).val * (b 25 j).val +
    (a i 26).val * (b 26 j).val) % 7 = (c i j).val
instance (a b c : Mat) : Decidable (NatProductEntries a b c) :=
  @Nat.decidableForallFin 27 _ (fun _i =>
    @Nat.decidableForallFin 27 _ (fun _j => inferInstance))
theorem mul_of_nat_entries (a b c : Mat) (h : NatProductEntries a b c) : a * b = c := by
  apply mul_of_entries
  intro i j
  have hh := congrArg (fun x : ℕ => (x : ZMod 7)) (h i j)
  simpa only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    ZMod.natCast_zmod_val] using hh

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
