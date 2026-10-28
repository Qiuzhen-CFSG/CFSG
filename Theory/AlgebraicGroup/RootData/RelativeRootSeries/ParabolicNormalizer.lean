module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicBounds
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicLevi

universe u

set_option linter.style.haveILetI false

/-!
Normalization of standard-parabolic relative-root layers by the root-generated
unipotent and parabolic point factors.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The root-generated standard unipotent factor is the first relative-root
layer. -/
public lemma standardUnipotentRootFactor_eq_firstRelativeRootLayer
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) :
    standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ = S.layer 1 := by
  rw [standardUnipotentRootFactor, ← S.unipotentRootGeneration,
    standardParabolicUnipotentRadical_eq_firstRelativeRootLayer S]

/-- The root-generated standard unipotent factor normalizes every
relative-root layer. -/
public lemma standardUnipotentRootFactor_le_relativeRootLayer_normalizer
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) :
    standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ ≤
      Subgroup.normalizer (S.layer i : Set (Variety.Point K)) := by
  rw [standardUnipotentRootFactor, ← S.unipotentRootGeneration]
  cases i with
  | zero =>
      rw [standardParabolicUnipotentRadical_eq_firstRelativeRootLayer S]
      exact (standardParabolicRelativeRootLayer_succ_le S 0).trans
        (S.layer 0).le_normalizer
  | succ i =>
      rw [Subgroup.le_normalizer_iff_commutator_le_left]
      exact (standardParabolicRelativeRootLayer_commutator_le_next S (i + 1)
        (by omega)).trans (standardParabolicRelativeRootLayer_succ_le S (i + 1))

/-- The abstract root-generated standard parabolic factor normalizes every
relative-root layer. -/
public lemma standardParabolicRootFactor_le_relativeRootLayer_normalizer
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) :
    standardParabolicRootFactor S.D S.positiveRoots S.sigmaJ ≤
      Subgroup.normalizer (S.layer i : Set (Variety.Point K)) := by
  rw [standardParabolicRootFactor, RootSubgroupGenerated_le_iff]
  intro α hα
  rcases hα with (hα | hα) | hα
  · by_cases hαLevi : α ∈ S.sigmaJ
    · exact (rootSubgroup_le_RootSubgroupGenerated S.D
        (A := S.sigmaJ ∪ S.D.neg '' S.sigmaJ) (Or.inl hαLevi)).trans
        (standardLeviRootFactor_le_relativeRootLayer_normalizer S i)
    · exact (rootSubgroup_le_RootSubgroupGenerated S.D
        (A := S.positiveRoots \ S.sigmaJ) ⟨hα, hαLevi⟩).trans
        (standardUnipotentRootFactor_le_relativeRootLayer_normalizer S i)
  · exact (rootSubgroup_le_RootSubgroupGenerated S.D
      (A := S.sigmaJ ∪ S.D.neg '' S.sigmaJ) (Or.inl hα)).trans
      (standardLeviRootFactor_le_relativeRootLayer_normalizer S i)
  · exact (rootSubgroup_le_RootSubgroupGenerated S.D
      (A := S.sigmaJ ∪ S.D.neg '' S.sigmaJ) (Or.inr hα)).trans
      (standardLeviRootFactor_le_relativeRootLayer_normalizer S i)

/-- Every positive relative-root layer is normal in the abstract
root-generated standard parabolic factor. -/
public lemma
    standardParabolicRelativeRootLayer_normal_in_standardParabolicRootFactor
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    ((S.layer i).subgroupOf
      (standardParabolicRootFactor S.D S.positiveRoots S.sigmaJ)).Normal := by
  letI := Fintype.ofFinite S.ι
  have hLayerLeFirst : S.layer i ≤ S.layer 1 :=
    relativeRootSeries_antitone S.D S.rootEquiv S.rationalBase.support
      S.coeff S.J (Nat.succ_le_iff.mp hi)
  have hLayerLeParabolic :
      S.layer i ≤ standardParabolicRootFactor S.D S.positiveRoots S.sigmaJ :=
    hLayerLeFirst.trans
      ((standardUnipotentRootFactor_eq_firstRelativeRootLayer S).ge.trans
        (standardUnipotentRootFactor_le_standardParabolicRootFactor S.D
          S.positiveRoots S.sigmaJ))
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLayerLeParabolic).2
    (standardParabolicRootFactor_le_relativeRootLayer_normalizer S i)

end Theory.AlgebraicGroup
