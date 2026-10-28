module

public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup
public import Theory.AlgebraicGroup.RootSubgroups.InvariantUnipotentOneParameterLayer
public import Theory.AlgebraicGroup.RootSubgroups.MultiplicityOne

universe u

/-! Root-subgroup weights and generation of invariant unipotent subgroups. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A torus root subgroup determines a unique torus weight whose point
character describes conjugation in every one-parameter parametrization.

This is GLS3, Proposition 1.9.2. -/
public theorem existsUnique_rootWeight_of_isTorusRootSubgroup
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (hX : IsTorusRootSubgroup T X) :
    ∃! χ : TorusWeight T, RootWeightEquation T X χ := by
  let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
  let χ : TorusWeight T := rootConjugationCharacter T X x hX.1
  have hEq : RootWeightEquation T X χ := by
    intro y t s
    rcases oneParameterParametrization_eq_rescale x y with ⟨c, hc, hcy⟩
    have hinc (z : Variety.Point X.carrierVariety) :
        X.includePoint z = X.inclusion.onPoints z := by
      apply Variety.Point.ext
      funext i
      rfl
    have h := rootConjugationScalar_ambient_action T X x hX.1 s (c * t)
    have hleft : X.includePoint (y.value t) =
        X.inclusion.onPoints (x.value (c * t)) := by
      exact (hinc _).trans (congrArg X.inclusion.onPoints (hc.2 t))
    have hright : X.includePoint (y.value (χ.pointCharacter s * t)) =
        X.inclusion.onPoints (x.value (c * (χ.pointCharacter s * t))) := by
      exact (hinc _).trans
        (congrArg X.inclusion.onPoints (hc.2 _))
    have hχs : χ.pointCharacter s =
        rootConjugationScalar T X x hX.1 s := by
      rfl
    rw [hleft, hright, hχs]
    change (T.inclusion.onPoints s)⁻¹ *
        X.inclusion.onPoints (x.value (c * t)) * T.inclusion.onPoints s = _
    rw [← h]
    congr 2
    ring_nf
  refine ⟨χ, hEq, ?_⟩
  intro ψ hψ
  exact rootWeightEquation_unique T X hX.2 hψ hEq

omit [IsAlgClosed k] in
/-- A realized torus root has a unique root subgroup once the corresponding
root weight has multiplicity one. -/
public theorem existsUnique_rootSubgroup_of_root_of_multiplicityOne
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (χ : TorusWeight T) (hχ : IsTorusRoot T χ)
    (hmult : RootWeightSpaceMultiplicityOne T χ) :
    ∃! X : ClosedSubgroup K,
      IsTorusRootSubgroup T X ∧ RootWeightEquation T X χ := by
  obtain ⟨X, hX, hXχ⟩ := hχ
  refine ⟨X, ⟨hX, hXχ⟩, ?_⟩
  intro Y hY
  exact hmult.rootSubgroup_eq hY.1 hY.2 hX hXχ

private lemma exists_missing_rootSubgroup
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (H : Subgroup (Variety.Point K))
    (hLayer : H < X.toSubgroup ∧ ∃ Y : ClosedSubgroup K,
      IsClosedSubgroupInvariant T Y ∧
      IsOneParameterGroup Y.carrierVariety ∧
      Y.toSubgroup ≤ X.toSubgroup ∧
      ¬ Y.toSubgroup ≤ H)
    (hsameWeight : ∀ {Y : ClosedSubgroup K} {α : D.Root},
      IsTorusRootSubgroup T Y →
      RootWeightEquation T Y (D.rootWeight α) →
      Y = D.rootSubgroup α) :
    ∃ α : D.Root,
      (D.rootSubgroup α).toSubgroup ≤ X.toSubgroup ∧
      ¬ (D.rootSubgroup α).toSubgroup ≤ H := by
  obtain ⟨_, Y, hYInvariant, hYOne, hYX, hYH⟩ := hLayer
  have hYRoot : IsTorusRootSubgroup T Y := ⟨hYInvariant, hYOne⟩
  obtain ⟨χ, hYχ, _⟩ :=
    existsUnique_rootWeight_of_isTorusRootSubgroup T Y hYRoot
  have hχRoot : χ ∈ TorusRootSet T := ⟨Y, hYRoot, hYχ⟩
  rw [← hD.2.1] at hχRoot
  obtain ⟨α, hαχ⟩ := hχRoot
  have hYα : Y = D.rootSubgroup α := by
    apply hsameWeight hYRoot
    simpa [hαχ] using hYχ
  subst Y
  exact ⟨α, hYX, hYH⟩

/-- A proper invariant one-parameter layer misses a realized root subgroup,
provided root subgroups with the same weight are unique. -/
public lemma exists_rootSubgroup_not_le_of_proper_invariant_oneParameter_layer
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (H : Subgroup (Variety.Point K))
    (hLayer : H < X.toSubgroup ∧ ∃ Y : ClosedSubgroup K,
      IsClosedSubgroupInvariant T Y ∧
      IsOneParameterGroup Y.carrierVariety ∧
      Y.toSubgroup ≤ X.toSubgroup ∧
      ¬ Y.toSubgroup ≤ H)
    (hsameWeight : ∀ {Y : ClosedSubgroup K} {α : D.Root},
      IsTorusRootSubgroup T Y →
      RootWeightEquation T Y (D.rootWeight α) →
      Y = D.rootSubgroup α) :
    ∃ α : D.Root,
      (D.rootSubgroup α).toSubgroup ≤ X.toSubgroup ∧
      ¬ (D.rootSubgroup α).toSubgroup ≤ H := by
  exact exists_missing_rootSubgroup T X D hD H hLayer hsameWeight

omit [IsAlgClosed k] in
private lemma closedSubgroup_le_rootSubgroupGenerated_of_exists_missing_root_of_lt
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (X : ClosedSubgroup K)
    (hmissing :
      RootSubgroupGenerated D
          {α | (D.rootSubgroup α).toSubgroup ≤ X.toSubgroup} < X.toSubgroup →
        ∃ α, (D.rootSubgroup α).toSubgroup ≤ X.toSubgroup ∧
          ¬(D.rootSubgroup α).toSubgroup ≤
            RootSubgroupGenerated D
              {β | (D.rootSubgroup β).toSubgroup ≤ X.toSubgroup}) :
    X.toSubgroup ≤ RootSubgroupGenerated D
      {α | (D.rootSubgroup α).toSubgroup ≤ X.toSubgroup} := by
  let A : Set D.Root :=
    {α | (D.rootSubgroup α).toSubgroup ≤ X.toSubgroup}
  have hgenerated : RootSubgroupGenerated D A ≤ X.toSubgroup :=
    RootSubgroupGenerated_le_of_rootSubgroup_le D A X.toSubgroup fun _ hα => hα
  by_contra hnot
  have hlt : RootSubgroupGenerated D A < X.toSubgroup := ⟨hgenerated, hnot⟩
  obtain ⟨α, hαX, hαmissing⟩ := hmissing hlt
  exact hαmissing (rootSubgroup_le_RootSubgroupGenerated D hαX)

/-- Theorem 1.9.5(i): an invariant unipotent subgroup is generated by the root
subgroups it contains, under the explicit one-parameter-layer and root-weight
uniqueness hypotheses used by the source argument. -/
public theorem invariant_unipotent_generated_by_rootSubgroups
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (D : RootGroupData K T) (_hK : IsReductiveAlgebraicGroup K)
    (_hT : IsMaximalTorus T) (hD : D.IsRealization)
    (_hX : IsClosedSubgroupInvariant T X)
    (_hXu : IsUnipotentAlgebraicGroup X.carrierVariety)
    (hLayer : HasInvariantOneParameterLayerOutsideGeneratedRoots T X D)
    (hsameWeight : ∀ {Y : ClosedSubgroup K} {α : D.Root},
      IsTorusRootSubgroup T Y →
      RootWeightEquation T Y (D.rootWeight α) →
      Y = D.rootSubgroup α) :
    ∃ A : Set D.Root,
      (∀ α, α ∈ A ↔ D.rootSubgroup α ≤ X) ∧
      X.toSubgroup = RootSubgroupGenerated D A := by
  let A : Set D.Root :=
    {α | (D.rootSubgroup α).toSubgroup ≤ X.toSubgroup}
  have hA : ∀ α, α ∈ A ↔ D.rootSubgroup α ≤ X := by
    intro α
    rfl
  have hgenerated : RootSubgroupGenerated D A ≤ X.toSubgroup := by
    apply RootSubgroupGenerated_le_of_rootSubgroup_le D A X.toSubgroup
    intro α hα
    exact hα
  have hreverse : X.toSubgroup ≤ RootSubgroupGenerated D A := by
    apply closedSubgroup_le_rootSubgroupGenerated_of_exists_missing_root_of_lt D X
    intro hlt
    apply exists_missing_rootSubgroup T X D hD (RootSubgroupGenerated D A)
    · exact ⟨hlt, hLayer.exists_layer T X D hlt⟩
    · exact hsameWeight
  exact ⟨A, hA, le_antisymm hreverse hgenerated⟩

/-- Multiplicity one supplies the root-subgroup uniqueness input in the
generation theorem. -/
public theorem invariant_unipotent_generated_by_rootSubgroups_of_multiplicityOne
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (D : RootGroupData K T) (hK : IsReductiveAlgebraicGroup K)
    (hT : IsMaximalTorus T) (hD : D.IsRealization)
    (hX : IsClosedSubgroupInvariant T X)
    (hXu : IsUnipotentAlgebraicGroup X.carrierVariety)
    (hLayer : HasInvariantOneParameterLayerOutsideGeneratedRoots T X D)
    (hmult : ∀ α : D.Root,
      RootWeightSpaceMultiplicityOne T (D.rootWeight α)) :
    ∃ A : Set D.Root,
      (∀ α, α ∈ A ↔ D.rootSubgroup α ≤ X) ∧
      X.toSubgroup = RootSubgroupGenerated D A := by
  apply invariant_unipotent_generated_by_rootSubgroups
    T X D hK hT hD hX hXu hLayer
  intro Y α hY hYχ
  exact RootWeightSpaceMultiplicityOne.rootSubgroup_eq
    (hmult α) hY hYχ (hD.2.2.1 α).1 (hD.2.2.1 α).2

end

end Theory.AlgebraicGroup
