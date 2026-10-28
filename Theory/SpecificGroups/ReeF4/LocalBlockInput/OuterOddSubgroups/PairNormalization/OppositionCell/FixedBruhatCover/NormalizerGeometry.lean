module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.Matrices
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.Grading
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.Transport
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneColumns
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport

/-!
# Normalizer-word geometry from the rank-one matrix calculations

Nonzero root-column scalars propagate through products and inverses. Positive
root curves are unitriangular for height, so two root-monomial matrices in
the same positive-unipotent double coset are equal. This identifies the actual
middle matrix, including its torus factor, even with unrestricted positive
right factors. Restricting those factors to `U ∩ n⁻¹U⁻n` gives the middle-factor
uniqueness required by fixed-point Bruhat descent.

The generator calculations in `RankOneColumns` and `RankOneTransport` apply
to each actual word `x_r(t) x_{-r}(-t⁻¹) x_r(t)`, for every root and every
nonzero parameter. Subgroup closure propagates their matrix action and exact
left conjugation on all root curves, with a root permutation and unit scalars.
The final theorems discharge both generator premises and hold for every `m`,
including `m = 0`. They require no coverage hypothesis.

Source: GLS3 1.11.5, 1.12.1(h), 2.3.5 and 2.3.8(b),
`refs/KGroup/GLS3/Chapter1.tex` and `chapter2.tex`.
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open LargeLocalSeeds NormalizerGeometry

/-- Root-monomial action of each actual generator suffices for all normalizer
words. This premise retains arbitrary nonzero parameters and torus words. -/
theorem splitNormalizerWords_rootMonomial_of_rankOne {m : ℕ}
    (hgen : ∀ (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ),
      IsRootMonomial (rankOneRepresentative m r t).val.val)
    {n : SplitGroup m} (hn : n ∈ splitNormalizerWords m) :
    IsRootMonomial n.val.val := by
  induction hn using Subgroup.closure_induction with
  | mem n hn =>
    obtain ⟨r, t, rfl⟩ := hn
    exact hgen r t
  | one => exact isRootMonomial_one
  | mul n k _ _ hn hk => exact hn.mul hk
  | inv n _ hn => exact hn.inv

/-- Positive unitriangular multiplication cannot change a root-monomial
matrix, including any of its nonzero root-column scalars. -/
theorem rootMonomial_eq_of_unipotent_mul {m : ℕ} {a n n' b : SplitGroup m}
    (ha : a ∈ splitUnipotent m) (hb : b ∈ splitUnipotent m)
    (hn : IsRootMonomial n.val.val) (hn' : IsRootMonomial n'.val.val)
    (he : a * n = n' * b) : n = n' := by
  obtain ⟨e, s, hN⟩ := hn
  obtain ⟨f, t, hN'⟩ := hn'
  have hm : a.val.val * n.val.val = n'.val.val * b.val.val :=
    congrArg (fun x : SplitGroup m => x.val.val) he
  have h := rootMonomial_eq_of_triangular basisDegree basisDegree_cartan
    (splitUnipotent_entry ha) (splitUnipotent_entry hb) hN hN' hm
  exact Subtype.ext (Units.ext h)

/-- The rank-one root-monomial calculation implies separation of normalizer
words by positive-unipotent double cosets. No coverage assumption is used. -/
theorem middle_representative_unique_of_unipotent_of_rankOne {m : ℕ}
    (hgen : ∀ (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ),
      IsRootMonomial (rankOneRepresentative m r t).val.val)
    {u n v u' n' v' : SplitGroup m}
    (hu : u ∈ splitUnipotent m) (hn : n ∈ splitNormalizerWords m)
    (hv : v ∈ splitUnipotent m) (hu' : u' ∈ splitUnipotent m)
    (hn' : n' ∈ splitNormalizerWords m) (hv' : v' ∈ splitUnipotent m)
    (he : u * n * v = u' * n' * v') : n = n' := by
  apply rootMonomial_eq_of_unipotent_mul
    ((splitUnipotent m).mul_mem ((splitUnipotent m).inv_mem hu') hu)
    ((splitUnipotent m).mul_mem hv' ((splitUnipotent m).inv_mem hv))
    (splitNormalizerWords_rootMonomial_of_rankOne hgen hn)
    (splitNormalizerWords_rootMonomial_of_rankOne hgen hn')
  calc
    (u'⁻¹ * u) * n = u'⁻¹ * (u * n * v) * v⁻¹ := by group
    _ = n' * (v' * v⁻¹) := by rw [he]; group

/-- The exact middle-factor uniqueness premise consumed by fixed-point Bruhat
cover, conditional only on the rank-one root-monomial matrix calculation. -/
theorem middle_representative_unique_of_rankOne {m : ℕ}
    (hgen : ∀ (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ),
      IsRootMonomial (rankOneRepresentative m r t).val.val)
    {u n v u' n' v' : SplitGroup m}
    (hu : u ∈ splitUnipotent m) (hn : n ∈ splitNormalizerWords m)
    (hv : v ∈ rightUnipotent n) (hu' : u' ∈ splitUnipotent m)
    (hn' : n' ∈ splitNormalizerWords m) (hv' : v' ∈ rightUnipotent n')
    (he : u * n * v = u' * n' * v') : n = n' :=
  middle_representative_unique_of_unipotent_of_rankOne hgen hu hn hv.1 hu' hn' hv'.1 he

/-- Every word in the actual rank-one generators has nonzero monomial root
columns and preserves the Cartan subspace, including words with torus factors. -/
theorem splitNormalizerWords_rootMonomial {m : ℕ}
    {n : SplitGroup m} (hn : n ∈ splitNormalizerWords m) :
    IsRootMonomial n.val.val :=
  splitNormalizerWords_rootMonomial_of_rankOne (rankOneRepresentative_isRootMonomial m) hn

/-- Every normalizer word acts on all concrete root curves by a permutation
and nonzero parameter scalars under left conjugation. -/
theorem rootTransport_of_mem_splitNormalizerWords {m : ℕ}
    {n : SplitGroup m} (hn : n ∈ splitNormalizerWords m) :
    Nonempty (RootTransport n) :=
  rootTransport_of_mem_splitNormalizerWords_of_rankOne
    (rootTransport_rankOneRepresentative m) hn

/-- Positive-unipotent double cosets separate actual normalizer words,
including their torus factors. Both right factors may be arbitrary in `U`. -/
theorem middle_representative_unique_of_unipotent {m : ℕ}
    {u n v u' n' v' : SplitGroup m}
    (hu : u ∈ splitUnipotent m) (hn : n ∈ splitNormalizerWords m)
    (hv : v ∈ splitUnipotent m) (hu' : u' ∈ splitUnipotent m)
    (hn' : n' ∈ splitNormalizerWords m) (hv' : v' ∈ splitUnipotent m)
    (he : u * n * v = u' * n' * v') : n = n' :=
  middle_representative_unique_of_unipotent_of_rankOne
    (rankOneRepresentative_isRootMonomial m) hu hn hv hu' hn' hv' he

/-- The unconditional middle-factor uniqueness premise for fixed-point
Bruhat descent, with the right factors in `U ∩ n⁻¹U⁻n`. -/
theorem middle_representative_unique {m : ℕ}
    {u n v u' n' v' : SplitGroup m}
    (hu : u ∈ splitUnipotent m) (hn : n ∈ splitNormalizerWords m)
    (hv : v ∈ rightUnipotent n) (hu' : u' ∈ splitUnipotent m)
    (hn' : n' ∈ splitNormalizerWords m) (hv' : v' ∈ rightUnipotent n')
    (he : u * n * v = u' * n' * v') : n = n' :=
  middle_representative_unique_of_unipotent hu hn hv.1 hu' hn' hv'.1 he

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
