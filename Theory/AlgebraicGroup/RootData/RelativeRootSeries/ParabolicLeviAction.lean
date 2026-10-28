module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicLevi
public import Theory.AlgebraicGroup.RootData.StandardLevi
public import Theory.AlgebraicGroup.RootSubgroups.TorusGeneratedNormalizer

universe u

set_option linter.style.haveILetI false

/-!
The standard Levi point subgroup action on relative-root layers.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The chosen standard torus normalizes every relative-root layer. -/
public lemma standardParabolicTorus_le_relativeRootLayer_normalizer
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) :
    S.T.toSubgroup ≤
      Subgroup.normalizer (S.layer i : Set (Variety.Point K)) := by
  simpa [StandardParabolicRelativeRootSetup.layer, RelativeRootSeries] using
    torus_le_rootSubgroupGenerated_normalizer S.D
      S.standardParabolic.1.2.1
      {α | (i : ℤ) ≤ RelativeRootHeight S.coeff S.rationalBase.support
        (S.rootEquiv '' S.J) (S.rootEquiv α)}

/-- The standard Levi point subgroup normalizes every relative-root layer. -/
public lemma standardLeviSubgroup_le_relativeRootLayer_normalizer
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) :
    standardLeviSubgroup S.D S.sigmaJ ≤
      Subgroup.normalizer (S.layer i : Set (Variety.Point K)) := by
  rw [standardLeviSubgroup, sup_le_iff]
  exact ⟨standardParabolicTorus_le_relativeRootLayer_normalizer S i,
    standardLeviRootFactor_le_relativeRootLayer_normalizer S i⟩

/-- The standard Levi point subgroup acts by conjugation on every positive
adjacent quotient of the relative-root filtration. -/
@[reducible]
public noncomputable def standardLeviSubgroup_relativeRootLayer_quotientAction
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    MulDistribMulAction (standardLeviSubgroup S.D S.sigmaJ)
      (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) := by
  letI := Fintype.ofFinite S.ι
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  exact relativeRootSeries_quotient_conjugation_action S.D S.rationalPairing
    S.rootEquiv S.rationalBase S.coeff S.J i
    (standardLeviSubgroup S.D S.sigmaJ)
    (fun l j => standardLeviSubgroup_le_relativeRootLayer_normalizer S j l.2)
    (standardParabolicRelativeRootLayer_next_normal S i hi)

/-- The standard Levi action on an adjacent quotient is represented by
ambient conjugation. -/
public lemma standardLeviSubgroup_relativeRootLayer_quotientAction_mk
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (l : standardLeviSubgroup S.D S.sigmaJ) (x : S.layer i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    (standardLeviSubgroup_relativeRootLayer_quotientAction S i hi).smul l
        (QuotientGroup.mk' ((S.layer (i + 1)).subgroupOf (S.layer i)) x) =
      QuotientGroup.mk' ((S.layer (i + 1)).subgroupOf (S.layer i))
        ⟨l.1 * x.1 * l.1⁻¹, by
          have hnorm :=
            standardLeviSubgroup_le_relativeRootLayer_normalizer S i l.2
          rw [Subgroup.mem_normalizer_iff] at hnorm
          exact (hnorm x.1).mp x.2⟩ := by
  letI := Fintype.ofFinite S.ι
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  exact relativeRootSeries_quotient_conjugation_action_mk S.D
    S.rationalPairing S.rootEquiv S.rationalBase S.coeff S.J i
    (standardLeviSubgroup S.D S.sigmaJ)
    (fun a j => standardLeviSubgroup_le_relativeRootLayer_normalizer S j a.2)
    (standardParabolicRelativeRootLayer_next_normal S i hi) l x

end Theory.AlgebraicGroup
