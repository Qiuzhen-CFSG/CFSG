module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicQuotient
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.QuotientAction
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.StandardParabolic
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ZeroHeightNormalizer
public import Theory.AlgebraicGroup.RootData.StandardParabolicGenerated

universe u

set_option linter.style.haveILetI false

/-!
The root-generated standard Levi factor and its action on relative-root
layers.  This file does not identify the root factor with a full Levi subgroup
containing the torus.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Roots in the standard Levi subsystem have relative height zero. -/
public lemma standardParabolicLeviRoot_relativeHeight_eq_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) {α : S.D.Root}
    (hα : α ∈ S.sigmaJ) :
    RelativeRootHeight S.coeff S.rationalBase.support
      (S.rootEquiv '' S.J) (S.rootEquiv α) = 0 := by
  letI := Fintype.ofFinite S.D.Root
  letI := Fintype.ofFinite S.ι
  have hFiber := relativeRootFiber_zero_eq_standardLeviRoots
    S.T S.B S.D S.integralPairing S.integralBase S.rootEquiv
    S.weightEquiv S.positiveRoots S.J S.sigmaJ S.coeff
    S.actualRootDatum S.integralSimpleRootExpansion S.standardParabolic
  have hmem := Set.ext_iff.mp hFiber (S.rootEquiv α)
  have hprojection : RelativeRootProjection S.coeff
      (S.integralBase.support : Set S.ι) (S.rootEquiv '' S.J)
      (S.rootEquiv α) = 0 := by
    have hleft := hmem.mpr ⟨α, hα, rfl⟩
    simpa [RelativeRootFiber] using hleft
  rw [S.baseSupport_eq]
  exact relativeRootHeight_eq_zero_of_projection_eq_zero S.coeff
    S.integralBase.support (S.rootEquiv '' S.J) hprojection

/-- The root-generated standard Levi factor normalizes every relative-root
layer. -/
public lemma standardLeviRootFactor_le_relativeRootLayer_normalizer
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) :
    standardLeviRootFactor S.D S.sigmaJ ≤
      Subgroup.normalizer (S.layer i : Set (Variety.Point K)) := by
  letI := Fintype.ofFinite S.D.Root
  letI := Fintype.ofFinite S.ι
  rw [standardLeviRootFactor, RootSubgroupGenerated_le_iff]
  intro α hα
  have hzero : RelativeRootHeight S.coeff S.rationalBase.support
      (S.rootEquiv '' S.J) (S.rootEquiv α) = 0 := by
    rcases hα with hα | ⟨β, hβ, rfl⟩
    · exact standardParabolicLeviRoot_relativeHeight_eq_zero S hα
    · rw [S.rationalRootRealization.2.2.1 β,
        relativeRootHeight_reflectionPerm_self S.rationalPairing
          S.rationalBase (S.rootEquiv '' S.J) S.coeff
          S.rationalSimpleRootExpansion,
        standardParabolicLeviRoot_relativeHeight_eq_zero S hβ, neg_zero]
  cases i with
  | zero =>
      have hrootLe : (S.D.rootSubgroup α).toSubgroup ≤ S.layer 0 := by
        intro x hx
        rw [StandardParabolicRelativeRootSetup.layer, RelativeRootSeries,
          RootSubgroupGenerated]
        apply Subgroup.subset_closure
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨α, by omega, hx⟩
      exact hrootLe.trans (S.layer 0).le_normalizer
  | succ i =>
      exact rootSubgroup_le_normalizer_relativeRootSeries_of_height_zero
        S.D S.C S.rationalPairing S.rootEquiv S.rationalBase S.coeff
        S.rationalSimpleRootExpansion S.chevalleySystem S.J (i + 1)
        (Nat.succ_pos i) α hzero

/-- The root-generated standard Levi factor acts by conjugation on every
positive adjacent quotient of the relative-root filtration. -/
@[reducible]
public noncomputable def standardLeviRootFactor_relativeRootLayer_quotientAction
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    MulDistribMulAction (standardLeviRootFactor S.D S.sigmaJ)
      (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) := by
  letI := Fintype.ofFinite S.ι
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  exact relativeRootSeries_quotient_conjugation_action S.D S.rationalPairing
    S.rootEquiv S.rationalBase S.coeff S.J i
    (standardLeviRootFactor S.D S.sigmaJ)
    (fun l j => standardLeviRootFactor_le_relativeRootLayer_normalizer S j l.2)
    (standardParabolicRelativeRootLayer_next_normal S i hi)

/-- The root-factor action on an adjacent quotient is represented by ambient
conjugation. -/
public lemma standardLeviRootFactor_relativeRootLayer_quotientAction_mk
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (l : standardLeviRootFactor S.D S.sigmaJ) (x : S.layer i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    (standardLeviRootFactor_relativeRootLayer_quotientAction S i hi).smul l
        (QuotientGroup.mk' ((S.layer (i + 1)).subgroupOf (S.layer i)) x) =
      QuotientGroup.mk' ((S.layer (i + 1)).subgroupOf (S.layer i))
        ⟨l.1 * x.1 * l.1⁻¹, by
          have hnorm :=
            standardLeviRootFactor_le_relativeRootLayer_normalizer S i l.2
          rw [Subgroup.mem_normalizer_iff] at hnorm
          exact (hnorm x.1).mp x.2⟩ := by
  letI := Fintype.ofFinite S.ι
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  exact relativeRootSeries_quotient_conjugation_action_mk S.D
    S.rationalPairing S.rootEquiv S.rationalBase S.coeff S.J i
    (standardLeviRootFactor S.D S.sigmaJ)
    (fun a j => standardLeviRootFactor_le_relativeRootLayer_normalizer S j a.2)
    (standardParabolicRelativeRootLayer_next_normal S i hi) l x

end Theory.AlgebraicGroup
