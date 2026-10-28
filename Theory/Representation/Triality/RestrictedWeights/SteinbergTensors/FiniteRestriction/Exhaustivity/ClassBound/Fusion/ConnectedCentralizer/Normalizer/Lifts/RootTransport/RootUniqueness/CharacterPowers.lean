module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.RootTransport.UniquenessInput
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter

/-!
# Higher powers of actual D4 root characters

Evaluation on the actual root cocharacter gives the integral value `2 * n`
for the nth power of its root character. It is nonzero for positive n, and
for n at least two it exceeds every Cartan integer in a reduced root system.
Transport through the given D4 pairing therefore excludes both the trivial
character and every root character. This argument uses full algebraic torus
characters and remains valid in characteristic two.

Source: GLS3, Definitions 1.9.1--1.9.3 and Remarks 1.9.6,
`refs/KGroup/GLS3/Chapter1.tex`. These comparisons supply the higher-weight
exclusion in the tangent proof of Theorem 1.9.5(b).
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
namespace ClassBound.ConnectedCentralizer.Normalizer.RootUniqueness
omit [IsAlgClosed k] in
private theorem pairing_le_three (S : Geometry K) (a b : S.roots.Root) :
    S.roots.pairing a b ≤ 3 := by
  have heq : S.roots.pairing a b =
      (typeDRootPairing 2).pairingIn ℤ (S.rootIndex a) (S.rootIndex b) := by
    apply Int.cast_injective (α := ℝ)
    rw [S.based.1, ← (typeDRootPairing 2).algebraMap_pairingIn ℤ]
    rfl
  rw [heq]
  have h := (typeDRootPairing 2).pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed
    (S.rootIndex a) (S.rootIndex b)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  omega

private theorem rootWeight_pow_pairing (S : Geometry K) (a : S.roots.Root) (n : ℕ) :
    S.roots.weightPairing (S.roots.rootWeight a ^ n) a = (n : ℤ) * 2 := by
  rw [S.realized.weightPairing_eq_characterCorootPairing]
  have h := (S.roots.characterCorootPairing a).map_nsmul n
    (Additive.ofMul (S.roots.rootWeight a))
  change S.roots.characterCorootPairing a
    (Additive.ofMul (S.roots.rootWeight a ^ n)) = _ at h
  rw [h, S.realized.characterCorootPairing_rootWeight,
    S.realized.2.2.2.2.2.2.1 a]
  simp

/-- Every positive power of an actual root character is nontrivial. -/
public theorem rootWeight_pow_ne_one (S : Geometry K) (a : S.roots.Root)
    {n : ℕ} (hn : n ≠ 0) : S.roots.rootWeight a ^ n ≠ 1 := by
  intro h
  have hp := rootWeight_pow_pairing S a n
  rw [h, S.realized.weightPairing_one] at hp
  omega

/-- A higher power of an actual root character is not an actual root character. -/
public theorem rootWeight_pow_ne_rootWeight (S : Geometry K) (a b : S.roots.Root)
    {n : ℕ} (hn : 2 ≤ n) : S.roots.rootWeight a ^ n ≠ S.roots.rootWeight b := by
  intro h
  have hp := rootWeight_pow_pairing S a n
  rw [h, S.realized.weightPairing_rootWeight] at hp
  have hbound := pairing_le_three S b a
  omega
end ClassBound.ConnectedCentralizer.Normalizer.RootUniqueness
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
