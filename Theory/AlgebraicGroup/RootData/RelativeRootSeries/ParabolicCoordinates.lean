module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicQuotient

universe u

set_option linter.style.haveILetI false

/-!
Exact-height root coordinates on adjacent standard-parabolic relative-root
quotients.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The quotient images of Chevalley root parameters whose relative height is
exactly `i`. -/
public noncomputable def
    standardParabolicRelativeRootLayer_exactHeightCoordinates
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    Set (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) := by
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  exact {q | ∃ (α : S.D.Root)
      (_ : RelativeRootHeight S.coeff S.rationalBase.support
        (S.rootEquiv '' S.J) (S.rootEquiv α) = i) (t : k),
      q = QuotientGroup.mk'
        ((S.layer (i + 1)).subgroupOf (S.layer i))
        ⟨S.C.x α t, by
          rw [StandardParabolicRelativeRootSetup.layer, RelativeRootSeries,
            RootSubgroupGenerated]
          apply Subgroup.subset_closure
          simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
          refine ⟨α, by omega, ?_⟩
          rw [← (S.chevalleySystem.1 α).2]
          exact ⟨t, rfl⟩⟩}

/-- Membership in the exact-height coordinate set. -/
public lemma mem_standardParabolicRelativeRootLayer_exactHeightCoordinates
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    ∀ q : S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i),
    q ∈ standardParabolicRelativeRootLayer_exactHeightCoordinates S i hi ↔
      ∃ (α : S.D.Root)
        (_ : RelativeRootHeight S.coeff S.rationalBase.support
          (S.rootEquiv '' S.J) (S.rootEquiv α) = i) (t : k),
        q = QuotientGroup.mk'
          ((S.layer (i + 1)).subgroupOf (S.layer i))
          ⟨S.C.x α t, by
            rw [StandardParabolicRelativeRootSetup.layer, RelativeRootSeries,
              RootSubgroupGenerated]
            apply Subgroup.subset_closure
            simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
            refine ⟨α, by omega, ?_⟩
            rw [← (S.chevalleySystem.1 α).2]
            exact ⟨t, rfl⟩⟩ := by
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  intro q
  rfl

/-- Exact-height Chevalley root coordinates generate the entire positive
adjacent quotient.  This is a generation statement, not uniqueness of root
coordinates. -/
public lemma
    standardParabolicRelativeRootLayer_exactHeightCoordinates_closure_eq_top
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    Subgroup.closure
      (standardParabolicRelativeRootLayer_exactHeightCoordinates S i hi) = ⊤ := by
  letI := Fintype.ofFinite S.ι
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  let N := (S.layer (i + 1)).subgroupOf (S.layer i)
  let H : Subgroup (S.layer i ⧸ N) :=
    Subgroup.closure
      (standardParabolicRelativeRootLayer_exactHeightCoordinates S i hi)
  apply le_antisymm le_top
  intro q hq
  refine QuotientGroup.induction_on q ?_
  intro x
  change QuotientGroup.mk' N x ∈ H
  have hx := x.2
  change x.1 ∈ RelativeRootSeries S.D S.rootEquiv S.rationalBase.support
    S.coeff S.J i at hx
  rw [RelativeRootSeries, RootSubgroupGenerated] at hx
  refine Subgroup.closure_induction
    (p := fun y hy =>
      QuotientGroup.mk' N
        (⟨y, by
          change y ∈ RelativeRootSeries S.D S.rootEquiv
            S.rationalBase.support S.coeff S.J i
          simpa [RelativeRootSeries, RootSubgroupGenerated] using hy⟩ :
          S.layer i) ∈ H)
    (k := ⋃ α ∈ {α | (i : ℤ) ≤ RelativeRootHeight S.coeff
      S.rationalBase.support (S.rootEquiv '' S.J) (S.rootEquiv α)},
      ↑(S.D.rootSubgroup α : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hy
    rcases hy with ⟨α, hα, hyα⟩
    by_cases hαeq : RelativeRootHeight S.coeff S.rationalBase.support
        (S.rootEquiv '' S.J) (S.rootEquiv α) = i
    · have hyRange : y ∈ Set.range (S.C.x α) := by
        rw [(S.chevalleySystem.1 α).2]
        exact hyα
      obtain ⟨t, rfl⟩ := hyRange
      apply Subgroup.subset_closure
      exact ⟨α, hαeq, t, rfl⟩
    · have hnext : (i + 1 : ℤ) ≤ RelativeRootHeight S.coeff
          S.rationalBase.support (S.rootEquiv '' S.J) (S.rootEquiv α) := by
        omega
      have hynext : y ∈ S.layer (i + 1) := by
        rw [StandardParabolicRelativeRootSetup.layer, RelativeRootSeries,
          RootSubgroupGenerated]
        apply Subgroup.subset_closure
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨α, hnext, hyα⟩
      have hone : QuotientGroup.mk' N
          (⟨y, by
            change y ∈ RelativeRootSeries S.D S.rootEquiv
              S.rationalBase.support S.coeff S.J i
            rw [RelativeRootSeries, RootSubgroupGenerated]
            apply Subgroup.subset_closure
            simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
            exact ⟨α, hα, hyα⟩⟩ : S.layer i) = 1 := by
        apply (QuotientGroup.eq_one_iff _).2
        exact hynext
      rw [hone]
      exact H.one_mem
  · change QuotientGroup.mk' N
      (⟨1, by simp [StandardParabolicRelativeRootSetup.layer,
        RelativeRootSeries, RootSubgroupGenerated]⟩ : S.layer i) ∈ H
    have heq : (⟨1, by simp [StandardParabolicRelativeRootSetup.layer,
        RelativeRootSeries, RootSubgroupGenerated]⟩ : S.layer i) = 1 := rfl
    rw [heq, map_one]
    exact H.one_mem
  · intro y z hy hz ihy ihz
    have heq :
        (⟨y * z, by
          change y * z ∈ RelativeRootSeries S.D S.rootEquiv
            S.rationalBase.support S.coeff S.J i
          simpa [RelativeRootSeries, RootSubgroupGenerated] using
            Subgroup.mul_mem _ hy hz⟩ : S.layer i) =
          (⟨y, by
            change y ∈ RelativeRootSeries S.D S.rootEquiv
              S.rationalBase.support S.coeff S.J i
            simpa [RelativeRootSeries, RootSubgroupGenerated] using hy⟩ :
            S.layer i) *
          (⟨z, by
            change z ∈ RelativeRootSeries S.D S.rootEquiv
              S.rationalBase.support S.coeff S.J i
            simpa [RelativeRootSeries, RootSubgroupGenerated] using hz⟩ :
            S.layer i) := rfl
    rw [heq, map_mul]
    exact H.mul_mem ihy ihz
  · intro y hy ihy
    have heq :
        (⟨y⁻¹, by
          change y⁻¹ ∈ RelativeRootSeries S.D S.rootEquiv
            S.rationalBase.support S.coeff S.J i
          simpa [RelativeRootSeries, RootSubgroupGenerated] using
            Subgroup.inv_mem _ hy⟩ : S.layer i) =
          (⟨y, by
            change y ∈ RelativeRootSeries S.D S.rootEquiv
              S.rationalBase.support S.coeff S.J i
            simpa [RelativeRootSeries, RootSubgroupGenerated] using hy⟩ :
            S.layer i)⁻¹ := rfl
    rw [heq, map_inv]
    exact H.inv_mem ihy

end Theory.AlgebraicGroup
