module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Geometry
public import Theory.AlgebraicGroup.Borel.RootNormalizer

/-!
# Normalizer reduction for the two supplied D4 root radicals

Both root-generated subgroups are the unipotent radicals of the actual Borels
in `Geometry.bigCell`. Their relative normality gives the lower normalizer
bounds unconditionally. The upper bounds follow from Bruhat coverage and
Borel self-normalization via `Borel.RootNormalizer`.

Those two geometric inputs remain explicit in the equality theorems below;
this is not yet an unconditional proof for every `Geometry`.

Sources: GLS3, Chapter 1, Theorem 1.6.3, and Steinberg (6.2)--(6.3) in
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

/-- The supplied positive Borel normalizes the actual positive root radical. -/
public theorem Geometry.borel_le_positive_normalizer (S : Geometry K) :
    S.bigCell.data.B.toSubgroup ≤ Subgroup.normalizer
      (RootSubgroupGenerated S.roots S.roots.positive : Set (Variety.Point K)) :=
  S.bigCell.data.positive_witness.le_rootGenerated_normalizer

/-- The supplied opposite Borel normalizes the actual negative root radical. -/
public theorem Geometry.oppositeBorel_le_negative_normalizer (S : Geometry K) :
    S.bigCell.data.Bopp.toSubgroup ≤ Subgroup.normalizer
      (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive) :
        Set (Variety.Point K)) :=
  S.bigCell.data.opposite_witness.le_rootGenerated_normalizer

/-- Positive normalizer equality conditional on actual Bruhat coverage and
self-normalization of the supplied positive Borel. -/
public theorem Geometry.positive_normalizer_eq_of_bruhat (S : Geometry K)
    (hcover : ∀ g : Variety.Point K, ∃ b n c : Variety.Point K,
      b ∈ S.bigCell.data.B.toSubgroup ∧ n ∈ S.torus.normalizer.toSubgroup ∧
        c ∈ S.bigCell.data.B.toSubgroup ∧ g = b * n * c)
    (hself : S.bigCell.data.B.normalizer = S.bigCell.data.B) :
    Subgroup.normalizer
      (RootSubgroupGenerated S.roots S.roots.positive : Set (Variety.Point K)) =
      S.bigCell.data.B.toSubgroup :=
  S.bigCell.data.positive_witness.rootGenerated_normalizer_eq_of_bruhat hcover hself

/-- Negative normalizer equality conditional on actual Bruhat coverage and
self-normalization of the supplied opposite Borel. -/
public theorem Geometry.negative_normalizer_eq_of_bruhat (S : Geometry K)
    (hcover : ∀ g : Variety.Point K, ∃ b n c : Variety.Point K,
      b ∈ S.bigCell.data.Bopp.toSubgroup ∧ n ∈ S.torus.normalizer.toSubgroup ∧
        c ∈ S.bigCell.data.Bopp.toSubgroup ∧ g = b * n * c)
    (hself : S.bigCell.data.Bopp.normalizer = S.bigCell.data.Bopp) :
    Subgroup.normalizer
      (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive) :
        Set (Variety.Point K)) = S.bigCell.data.Bopp.toSubgroup :=
  S.bigCell.data.opposite_witness.rootGenerated_normalizer_eq_of_bruhat hcover hself

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
