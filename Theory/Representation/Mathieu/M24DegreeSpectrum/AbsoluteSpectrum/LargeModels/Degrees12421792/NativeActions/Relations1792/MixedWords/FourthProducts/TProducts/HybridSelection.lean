module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Hybrid

/-!
# Checked selection witnesses for hybrid rows

The exponent of a basis-vector row is supplied as an untrusted numerical
witness and certified by kernel checking. A second set bit certifies the
complementary branch. The logical logarithm is eliminated by proved identities,
so these proofs establish the same `Hybrid.row` equations as the original
checker. The concrete consumers are the Product modules of `TProducts`.
Source and measurements: `TProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Hybrid

theorem row_of_eq_pow (a k z : Nat) (ys : List Nat) (ws : List (List Nat))
    (hk : k < 1792) (ha : a = 2^k) (hz : ys[k]! = z) : row a ys ws = z := by
  rw [row, ha, Nat.log2_two_pow, if_pos ⟨rfl, hk⟩]
  exact hz

/-- A checked second set bit excludes the basis-vector branch without logarithm reduction. -/
theorem row_of_many_bits (a z : Nat) (ys : List Nat) (ws : List (List Nat))
    (ha : a &&& (a-1) ≠ 0) (hz : Arithmetic.row a ws = z) : row a ys ws = z := by
  have hn : a ≠ 2^a.log2 := by
    intro h
    have hh := congrArg (fun n : Nat => n &&& (n-1)) h
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self] at hh
    exact ha hh
  rw [row, if_neg (fun h => hn h.1)]
  exact hz

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Hybrid
