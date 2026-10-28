module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.Pair

/-!
# Small certificates in the faithful octonion representation

Each product is checked by eight-term dot products, avoiding repeated reduction
of long words in linear equivalences. A certified right inverse also computes
the image of an inverse automorphism. These lemmas are used on the literal
six ATLAS relators in `Relations.lean`.

The finite dot-product method follows the checked G₂(5) implementation in
`Theory/SpecificGroups/G2Five/AtlasOctonionRelationCertificate.lean`.
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison

def ProductEntries (a b c : Mat) : Prop :=
  ∀ i j, a i 0 * b 0 j + a i 1 * b 1 j + a i 2 * b 2 j +
    a i 3 * b 3 j + a i 4 * b 4 j + a i 5 * b 5 j +
    a i 6 * b 6 j + a i 7 * b 7 j = c i j

instance (a b c : Mat) : Decidable (ProductEntries a b c) :=
  @Nat.decidableForallFin 8 _ (fun _i =>
    @Nat.decidableForallFin 8 _ (fun _j => inferInstance))

theorem mul_of_entries {a b c : Mat} (h : ProductEntries a b c) : a * b = c := by
  ext i j
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, Fin.succ, add_assoc] using h i j

theorem mul_certificate {g h : Model (ZMod 3)} {a b c : Mat}
    (hg : coordinateMatrix g = a) (hh : coordinateMatrix h = b)
    (hp : ProductEntries a b c) : coordinateMatrix (g * h) = c := by
  rw [map_mul, hg, hh, mul_of_entries hp]

theorem inv_certificate {g : Model (ZMod 3)} {a b : Mat}
    (hg : coordinateMatrix g = a) (hp : ProductEntries a b 1) :
    coordinateMatrix g⁻¹ = b := by
  have h : coordinateMatrix g * b = 1 := by rw [hg, mul_of_entries hp]
  have hh := congrArg (coordinateMatrix g⁻¹ * ·) h
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul, mul_one]
    using hh.symm

theorem pow_certificate {g : Model (ZMod 3)} {a b c : Mat} {k l : ℕ}
    (hk : coordinateMatrix (g ^ k) = a) (hl : coordinateMatrix (g ^ l) = b)
    (hp : ProductEntries a b c) : coordinateMatrix (g ^ (k + l)) = c := by
  rw [pow_add]
  exact mul_certificate hk hl hp

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison
