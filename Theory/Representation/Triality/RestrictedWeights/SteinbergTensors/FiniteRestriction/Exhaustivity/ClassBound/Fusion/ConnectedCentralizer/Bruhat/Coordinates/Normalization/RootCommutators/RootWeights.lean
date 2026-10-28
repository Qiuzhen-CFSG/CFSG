module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.Basic
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter

/-!
# Actual character combinations and positive D4 roots

A positive integral identity of actual root characters gives the corresponding
identity of standard D4 root vectors. Evaluate the character identity on every
realized coroot; additivity of the integral character--cocharacter pairing and
nondegeneracy of the root pairing then identify the vectors. Base height shows
that a positive integral combination of positive roots is positive.

The result connects a geometric character-support calculation to precisely the
correction-root set in `Normalization.Basic`. It assumes no commutator formula.

Source: GLS3, Chapter 1, Remarks 1.9.6 and Theorem 1.12.7(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
namespace ConnectedCentralizer.Bruhat.Coordinates.Normalization
noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

private theorem weightPairing_pow (S : Geometry K) (χ : TorusWeight S.torus)
    (d : S.roots.Root) (n : ℕ) :
    S.roots.weightPairing (χ ^ n) d = n * S.roots.weightPairing χ d := by
  induction n with
  | zero => simp [S.realized.weightPairing_one]
  | succ n ih =>
    rw [pow_succ, S.realized.weightPairing_mul, ih]
    push_cast
    ring

/-- Actual character multiplication determines addition of standard root vectors. -/
public theorem root_eq_nat_combination_of_weight_eq (S : Geometry K)
    {a b c : S.roots.Root} {i j : ℕ}
    (h : S.roots.rootWeight c = S.roots.rootWeight a ^ i * S.roots.rootWeight b ^ j) :
    (typeDRootPairing 2).root (S.rootIndex c) =
      (i : ℝ) • (typeDRootPairing 2).root (S.rootIndex a) +
      (j : ℝ) • (typeDRootPairing 2).root (S.rootIndex b) := by
  let P := typeDRootPairing 2
  apply P.toPerfPair.injective
  apply LinearMap.ext_on (s := Set.range P.coroot)
    (RootPairing.IsRootSystem.span_coroot_eq_top (P := P))
  rintro _ ⟨d, rfl⟩
  change P.toLinearMap (P.root (S.rootIndex c)) (P.coroot d) =
    P.toLinearMap ((i : ℝ) • P.root (S.rootIndex a) +
      (j : ℝ) • P.root (S.rootIndex b)) (P.coroot d)
  have hd := congrArg (fun χ => S.roots.weightPairing χ (S.rootIndex.symm d)) h
  rw [S.realized.weightPairing_mul, weightPairing_pow, weightPairing_pow,
    S.realized.weightPairing_rootWeight, S.realized.weightPairing_rootWeight,
    S.realized.weightPairing_rootWeight] at hd
  have hd' := congrArg (fun z : ℤ => (z : ℝ)) hd
  push_cast at hd'
  simp only [S.based.1, Equiv.apply_symm_apply] at hd'
  simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    RootPairing.root_coroot_eq_pairing, smul_eq_mul] using hd'

private theorem height_nat_combination
    {a b c : TypeDRootIndex 4} {i j : ℕ}
    (h : (typeDRootPairing 2).root c =
      (i : ℝ) • (typeDRootPairing 2).root a +
      (j : ℝ) • (typeDRootPairing 2).root b) :
    (typeDRootPairing_base 2).height c =
      (i : ℤ) * (typeDRootPairing_base 2).height a +
      (j : ℤ) * (typeDRootPairing_base 2).height b := by
  classical
  let P := typeDRootPairing 2
  let base := typeDRootPairing_base 2
  obtain ⟨f, -, -, hf⟩ := base.exists_root_eq_sum_int a
  obtain ⟨g, -, -, hg⟩ := base.exists_root_eq_sum_int b
  have h' : P.root c = (i : ℤ) • P.root a + (j : ℤ) • P.root b := by
    have hn : P.root c = i • P.root a + j • P.root b := by
      simpa only [Nat.cast_smul_eq_nsmul ℝ] using h
    simpa only [natCast_zsmul] using hn
  have hc : P.root c = ∑ d ∈ base.support,
      ((i : ℤ) * f d + (j : ℤ) * g d) • P.root d := by
    rw [h', hf, hg]
    simp_rw [Finset.smul_sum, smul_smul, add_zsmul, Finset.sum_add_distrib]
    rfl
  rw [base.height_eq_sum hc, base.height_eq_sum hf, base.height_eq_sum hg]
  simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- A character with positive powers of two positive root characters indexes an
actual positive correction root in the published commutator support. -/
public theorem positiveCommutatorRoots_of_weight_eq (S : Geometry K)
    {a b c : S.roots.Root} (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive)
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (h : S.roots.rootWeight c = S.roots.rootWeight a ^ i * S.roots.rootWeight b ^ j) :
    c ∈ positiveCommutatorRoots S a b := by
  have hroot := root_eq_nat_combination_of_weight_eq S h
  refine ⟨?_, i, j, hi, hj, hroot⟩
  rw [S.positive, RootPairing.Base.isPos_iff]
  have ha' := (S.positive a).mp ha
  have hb' := (S.positive b).mp hb
  rw [RootPairing.Base.isPos_iff] at ha' hb'
  rw [height_nat_combination hroot]
  exact add_pos (mul_pos (by exact_mod_cast hi) ha')
    (mul_pos (by exact_mod_cast hj) hb')

end
end ConnectedCentralizer.Bruhat.Coordinates.Normalization
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
