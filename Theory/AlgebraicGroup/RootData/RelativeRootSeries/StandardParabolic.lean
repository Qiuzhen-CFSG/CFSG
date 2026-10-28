module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Basic
public import Theory.AlgebraicGroup.RootData.Standard

universe u

open scoped BigOperators

/-!
The first relative-root layer of a standard parabolic subgroup.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Roots with zero relative projection are exactly the roots in the
standard Levi subsystem. -/
public lemma relativeRootFiber_zero_eq_standardLeviRoots
    {K : Variety k} [AlgebraicGroup K] (T B : ClosedSubgroup K)
    (D : RootGroupData K T) [Fintype D.Root]
    {ι X Y : Type*} [Fintype ι] [AddCommGroup X] [AddCommGroup Y]
    (rootPairing : RootPairing ι ℤ X Y) [rootPairing.IsRootSystem]
    [rootPairing.IsCrystallographic] [rootPairing.IsReduced]
    (base : rootPairing.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (positiveRoots J sigmaJ : Set D.Root)
    (coeff : ι → ι → ℤ)
    (hActual : IsActualBasedRootDatum D rootPairing base e weightEquiv positiveRoots)
    (hCoeff : HasSimpleRootExpansion rootPairing base coeff)
    (hSetup : IsStandardParabolicSetup T B D positiveRoots J sigmaJ) :
    RelativeRootFiber coeff (base.support : Set ι) (e '' J) Set.univ 0 = e '' sigmaJ := by
  classical
  rcases hActual with ⟨hPairing, hDatum, _⟩
  have hJsimple : J ⊆ D.simple := hSetup.2.1
  have hsigma : sigmaJ = RootSubsystemSpan D J := hSetup.2.2
  have hCoeffUnique (β γ : ι) (hγ : γ ∈ base.support) {f : ι → ℤ}
      (hf : rootPairing.root β = ∑ j ∈ base.support, f j • rootPairing.root j) :
      coeff β γ = f γ := by
    have hc := (hCoeff β).1
    rw [base.support.sum_subtype (p := (· ∈ base.support)) (by simp)
      (F := inferInstance)] at hc hf
    have heq : ∑ j : base.support, coeff β j • rootPairing.root j =
        ∑ j : base.support, f j • rootPairing.root j := hc.symm.trans hf
    exact Fintype.linearIndependent_iffₛ.mp
      (base.linearIndepOn_root.restrict_scalars' ℤ)
      (fun j : base.support => coeff β j) (fun j : base.support => f j) heq ⟨γ, hγ⟩
  have hWeightSpan (α : D.Root) :
      D.rootWeight α ∈ Subgroup.closure (D.rootWeight '' J) ↔
        rootPairing.root (e α) ∈ AddSubgroup.closure (rootPairing.root '' (e '' J)) := by
    constructor
    · intro hα
      have hα' : Multiplicative.toAdd (weightEquiv.symm (D.rootWeight α)) ∈
          AddSubgroup.closure (rootPairing.root '' (e '' J)) := by
        exact Subgroup.closure_induction (p := fun x _ =>
          Multiplicative.toAdd (weightEquiv.symm x) ∈
            AddSubgroup.closure (rootPairing.root '' (e '' J)))
          (fun _ hx => by
            obtain ⟨β, hβJ, rfl⟩ := hx
            rw [← hDatum β, weightEquiv.symm_apply_apply]
            exact AddSubgroup.subset_closure ⟨e β, ⟨β, hβJ, rfl⟩, rfl⟩)
          (by simp)
          (fun _ _ _ _ hx hy => by simpa using AddSubgroup.add_mem _ hx hy)
          (fun _ _ hx => by simpa using AddSubgroup.neg_mem _ hx) hα
      rw [← hDatum α, weightEquiv.symm_apply_apply] at hα'
      exact hα'
    · intro hα
      have hα' : weightEquiv (Multiplicative.ofAdd (rootPairing.root (e α))) ∈
          Subgroup.closure (D.rootWeight '' J) := by
        exact AddSubgroup.closure_induction (p := fun x _ =>
          weightEquiv (Multiplicative.ofAdd x) ∈ Subgroup.closure (D.rootWeight '' J))
          (fun _ hx => by
            obtain ⟨δ, ⟨β, hβJ, rfl⟩, rfl⟩ := hx
            rw [hDatum β]
            exact (Subgroup.subset_closure ⟨β, hβJ, rfl⟩ :
              D.rootWeight β ∈ Subgroup.closure (D.rootWeight '' J)))
          (by simp)
          (fun _ _ _ _ hx hy => by simpa using Subgroup.mul_mem _ hx hy)
          (fun _ _ hx => by simpa using Subgroup.inv_mem _ hx) hα
      simpa [hDatum α] using hα'
  have hRootSpan (β : ι) :
      rootPairing.root β ∈ AddSubgroup.closure (rootPairing.root '' (e '' J)) ↔
        ∀ γ ∈ base.support, e.symm γ ∉ J → coeff β γ = 0 := by
    constructor
    · intro hβ
      have hrep : ∃ f : ι → ℤ,
          (∀ γ, γ ∉ base.support → f γ = 0) ∧
          (∀ γ ∈ base.support, e.symm γ ∉ J → f γ = 0) ∧
          rootPairing.root β = ∑ γ ∈ base.support, f γ • rootPairing.root γ := by
        exact AddSubgroup.closure_induction (p := fun x _ => ∃ f : ι → ℤ,
          (∀ γ, γ ∉ base.support → f γ = 0) ∧
          (∀ γ ∈ base.support, e.symm γ ∉ J → f γ = 0) ∧
          x = ∑ γ ∈ base.support, f γ • rootPairing.root γ)
          (fun _ hx => by
            obtain ⟨δ, hδJ, rfl⟩ := hx
            have hδSupport : δ ∈ base.support := by
              obtain ⟨α, hαJ, rfl⟩ := hδJ
              exact (hPairing.2.2.2 α).mp (hJsimple hαJ)
            refine ⟨Pi.single δ 1, ?_, ?_, ?_⟩
            · intro γ hγ
              by_cases hγδ : γ = δ
              · subst γ
                exact False.elim (hγ hδSupport)
              · simp [hγδ]
            · intro γ hγSupport hγJ
              by_cases hγδ : γ = δ
              · subst γ
                have hδJ' : e.symm δ ∈ J := by simpa using hδJ
                exact False.elim (hγJ hδJ')
              · simp [hγδ]
            · rw [Finset.sum_eq_single_of_mem δ hδSupport]
              · simp
              · intro γ hγSupport hγne
                simp [hγne])
          ⟨0, by simp, by simp, by simp⟩
          (fun _ _ _ _ ihx ihy => by
            obtain ⟨f, hfSupport, hfJ, hfx⟩ := ihx
            obtain ⟨g, hgSupport, hgJ, hgy⟩ := ihy
            refine ⟨f + g, ?_, ?_, ?_⟩
            · intro γ hγ
              simp [hfSupport γ hγ, hgSupport γ hγ]
            · intro γ hγSupport hγJ
              simp [hfJ γ hγSupport hγJ, hgJ γ hγSupport hγJ]
            · simp_rw [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← hfx, ← hgy])
          (fun _ _ ihx => by
            obtain ⟨f, hfSupport, hfJ, hfx⟩ := ihx
            refine ⟨-f, ?_, ?_, ?_⟩
            · intro γ hγ
              simp [hfSupport γ hγ]
            · intro γ hγSupport hγJ
              simp [hfJ γ hγSupport hγJ]
            · simp_rw [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, ← hfx]) hβ
      obtain ⟨f, -, hfJ, hfRoot⟩ := hrep
      intro γ hγSupport hγJ
      rw [hCoeffUnique β γ hγSupport hfRoot, hfJ γ hγSupport hγJ]
    · intro hβ
      rw [(hCoeff β).1]
      exact AddSubgroup.sum_mem _ fun γ hγSupport => by
        by_cases hγJ : e.symm γ ∈ J
        · have hγJ' : γ ∈ e '' J := by simpa
          have hroot : rootPairing.root γ ∈ rootPairing.root '' (e '' J) :=
            ⟨γ, hγJ', rfl⟩
          exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hroot) _
        · simp [hβ γ hγSupport hγJ]
  have hProjectionZero (β : ι) :
      RelativeRootProjection coeff (base.support : Set ι) (e '' J) β = 0 ↔
        rootPairing.root β ∈ AddSubgroup.closure (rootPairing.root '' (e '' J)) := by
    rw [hRootSpan]
    constructor
    · intro hzero γ hγSupport hγJ
      have hvalue := congrArg (fun f : ι →₀ ℤ => f γ) hzero
      simpa [RelativeRootProjection, hγSupport, hγJ] using hvalue
    · intro hzero
      apply Finsupp.ext
      intro γ
      by_cases hγSupport : γ ∈ base.support
      · by_cases hγJ : e.symm γ ∈ J
        · simp [RelativeRootProjection, hγSupport, hγJ]
        · simp [RelativeRootProjection, hγSupport, hγJ,
            hzero γ hγSupport hγJ]
      · simp [RelativeRootProjection, hγSupport]
  have hSubsystem (α : D.Root) :
      α ∈ sigmaJ ↔ RelativeRootProjection coeff (base.support : Set ι) (e '' J) (e α) = 0 := by
    rw [hsigma]
    exact (hWeightSpan α).trans (hProjectionZero (e α)).symm
  ext β
  simp only [RelativeRootFiber, Set.mem_ofPred_eq, Set.mem_univ, true_and]
  constructor
  · intro hβ
    refine ⟨e.symm β, (hSubsystem (e.symm β)).mpr ?_, by simp⟩
    simpa using hβ
  · rintro ⟨α, hασ, rfl⟩
    exact (hSubsystem α).mp hασ
end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- An actual based root datum identifies the roots of relative height at least one
with the positive roots outside the standard Levi subsystem. -/
private lemma heightOneRoots_eq_positiveRootsOutsideLevi
    {K : Variety k} [AlgebraicGroup K] (T B : ClosedSubgroup K)
    (D : RootGroupData K T) [Fintype D.Root]
    {ι X Y : Type*} [Fintype ι] [AddCommGroup X] [AddCommGroup Y]
    (rootPairing : RootPairing ι ℤ X Y) [rootPairing.IsRootSystem]
    [rootPairing.IsCrystallographic] [rootPairing.IsReduced]
    (base : rootPairing.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (positiveRoots J sigmaJ : Set D.Root)
    (coeff : ι → ι → ℤ)
    (hActual : IsActualBasedRootDatum D rootPairing base e weightEquiv positiveRoots)
    (hCoeff : HasSimpleRootExpansion rootPairing base coeff)
    (hSetup : IsStandardParabolicSetup T B D positiveRoots J sigmaJ) :
    {α | (1 : ℤ) ≤ RelativeRootHeight coeff base.support (e '' J) (e α)} =
      positiveRoots \ sigmaJ := by
  classical
  have hFiber := relativeRootFiber_zero_eq_standardLeviRoots T B D rootPairing base e
    weightEquiv positiveRoots J sigmaJ coeff hActual hCoeff hSetup
  have hPositive := hActual.2.2
  have hCoeffUnique (β γ : ι) (hγ : γ ∈ base.support) {f : ι → ℤ}
      (hf : rootPairing.root β = ∑ j ∈ base.support, f j • rootPairing.root j) :
      coeff β γ = f γ := by
    have hc := (hCoeff β).1
    rw [base.support.sum_subtype (p := (· ∈ base.support)) (by simp)
      (F := inferInstance)] at hc hf
    have heq : ∑ j : base.support, coeff β j • rootPairing.root j =
        ∑ j : base.support, f j • rootPairing.root j := hc.symm.trans hf
    exact Fintype.linearIndependent_iffₛ.mp
      (base.linearIndepOn_root.restrict_scalars' ℤ)
      (fun j : base.support => coeff β j) (fun j : base.support => f j) heq ⟨γ, hγ⟩
  have hCoeffSign (β : ι) : 0 < coeff β ∨ coeff β < 0 := by
    obtain ⟨f, hfSupport, hfSign, hfRoot⟩ := base.exists_root_eq_sum_int β
    have hcf : coeff β = f := by
      funext γ
      by_cases hγ : γ ∈ base.support
      · exact hCoeffUnique β γ hγ hfRoot
      · rw [(hCoeff β).2 γ hγ]
        exact (not_ne_iff.mp fun hfγ => hγ (hfSupport (Ne.symm hfγ)))
    simpa [hcf] using hfSign
  have hSubsystem (α : D.Root) :
      α ∈ sigmaJ ↔ RelativeRootProjection coeff (base.support : Set ι)
        (e '' J) (e α) = 0 := by
    have hmem := Set.ext_iff.mp hFiber (e α)
    simp only [RelativeRootFiber, Set.mem_ofPred_eq, Set.mem_univ, true_and] at hmem
    constructor
    · intro hα
      exact hmem.mpr ⟨α, hα, rfl⟩
    · intro hzero
      obtain ⟨β, hβ, hβα⟩ := hmem.mp hzero
      exact (e.injective hβα) ▸ hβ
  ext α
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
  have hsum : RelativeRootHeight coeff base.support (e '' J) (e α) =
      ∑ γ ∈ base.support, if γ ∉ e '' J then coeff (e α) γ else 0 := rfl
  constructor
  · intro hheight
    have hnotNeg : ¬ coeff (e α) < 0 := by
      intro hneg
      rw [hsum] at hheight
      have hnonpos : ∑ γ ∈ base.support,
          (if γ ∉ e '' J then coeff (e α) γ else 0) ≤ 0 :=
        Finset.sum_nonpos fun γ _ => by
          by_cases hγJ : γ ∉ e '' J
          · rw [if_pos hγJ]
            exact (Pi.lt_def.mp hneg).1 γ
          · rw [if_neg hγJ]
      omega
    have hpos : 0 < coeff (e α) := (hCoeffSign (e α)).resolve_right hnotNeg
    have hαPositive : α ∈ positiveRoots := by
      rw [hPositive α, RootPairing.Base.isPos_iff,
        base.height_eq_sum (hCoeff (e α)).1]
      obtain ⟨γ, hγPositive⟩ := (Pi.lt_def.mp hpos).2
      have hγSupport : γ ∈ base.support := by
        by_contra hγSupport
        rw [(hCoeff (e α)).2 γ hγSupport] at hγPositive
        simp at hγPositive
      exact Finset.sum_pos' (fun δ _ => (Pi.lt_def.mp hpos).1 δ)
        ⟨γ, hγSupport, hγPositive⟩
    refine ⟨hαPositive, ?_⟩
    intro hασ
    have hzero := (hSubsystem α).mp hασ
    have houtside : ∀ γ ∈ base.support, γ ∉ e '' J → coeff (e α) γ = 0 := by
      intro γ hγSupport hγJ
      have hγJ' : e.symm γ ∉ J := by simpa using hγJ
      have hvalue := congrArg (fun f : ι →₀ ℤ => f γ) hzero
      simpa [RelativeRootProjection, hγSupport, hγJ'] using hvalue
    rw [hsum] at hheight
    have hsumzero : ∑ γ ∈ base.support,
        (if γ ∉ e '' J then coeff (e α) γ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro γ hγSupport
      by_cases hγJ : γ ∉ e '' J
      · rw [if_pos hγJ, houtside γ hγSupport hγJ]
      · rw [if_neg hγJ]
    omega
  · rintro ⟨hαPositive, hασ⟩
    have hpos : 0 < coeff (e α) := by
      rcases hCoeffSign (e α) with hpos | hneg
      · exact hpos
      · rw [hPositive α, RootPairing.Base.isPos_iff,
          base.height_eq_sum (hCoeff (e α)).1] at hαPositive
        have hnonpos : ∑ γ ∈ base.support, coeff (e α) γ ≤ 0 :=
          Finset.sum_nonpos fun γ _ => (Pi.lt_def.mp hneg).1 γ
        exact (not_lt_of_ge hnonpos hαPositive).elim
    have hprojection : RelativeRootProjection coeff (base.support : Set ι)
        (e '' J) (e α) ≠ 0 := fun hzero => hασ ((hSubsystem α).mpr hzero)
    have hexists : ∃ γ ∈ base.support, γ ∉ e '' J ∧ coeff (e α) γ ≠ 0 := by
      by_contra hexists
      push Not at hexists
      apply hprojection
      apply Finsupp.ext
      intro γ
      by_cases hγSupport : γ ∈ base.support
      · by_cases hγJ : e.symm γ ∈ J
        · simp [RelativeRootProjection, hγSupport, hγJ]
        · have hγJ' : γ ∉ e '' J := by simpa
          simp [RelativeRootProjection, hγSupport, hγJ,
            hexists γ hγSupport hγJ']
      · simp [RelativeRootProjection, hγSupport]
    obtain ⟨γ, hγSupport, hγJ, hγne⟩ := hexists
    rw [hsum]
    have hnonneg : ∀ δ ∈ base.support,
        0 ≤ if δ ∉ e '' J then coeff (e α) δ else 0 := by
      intro δ hδSupport
      by_cases hδJ : δ ∉ e '' J
      · rw [if_pos hδJ]
        exact (Pi.lt_def.mp hpos).1 δ
      · rw [if_neg hδJ]
    have hpositive : 0 < if γ ∉ e '' J then coeff (e α) γ else 0 := by
      simp only [if_pos hγJ]
      exact lt_of_le_of_ne ((Pi.lt_def.mp hpos).1 γ) (Ne.symm hγne)
    exact Finset.sum_pos' hnonneg ⟨γ, hγSupport, hpositive⟩

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Under the source-faithful actual based root datum, the first relative-root
series subgroup is the standard parabolic unipotent factor. -/
public theorem relativeRootSeries_one_eq_standardUnipotentRadical
    {K : Variety k} [AlgebraicGroup K] (T B : ClosedSubgroup K)
    (D : RootGroupData K T) [Fintype D.Root]
    {ι X Y : Type*} [Fintype ι] [AddCommGroup X] [AddCommGroup Y]
    (rootPairing : RootPairing ι ℤ X Y) [rootPairing.IsRootSystem]
    [rootPairing.IsCrystallographic] [rootPairing.IsReduced]
    (base : rootPairing.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (positiveRoots J sigmaJ : Set D.Root) (U : ClosedSubgroup K)
    (coeff : ι → ι → ℤ)
    (hActual : IsActualBasedRootDatum D rootPairing base e weightEquiv positiveRoots)
    (hCoeff : HasSimpleRootExpansion rootPairing base coeff)
    (hSetup : IsStandardParabolicSetup T B D positiveRoots J sigmaJ)
    (hU : U.toSubgroup = RootSubgroupGenerated D (positiveRoots \ sigmaJ)) :
    RelativeRootSeries D e base.support coeff J 1 = U.toSubgroup := by
  apply relativeRootSeries_one_eq_of_root_set_eq D e base.support coeff J
    (positiveRoots \ sigmaJ) U.toSubgroup
  · exact heightOneRoots_eq_positiveRootsOutsideLevi
      T B D rootPairing base e weightEquiv positiveRoots J sigmaJ
      coeff hActual hCoeff hSetup
  · exact hU

end
end Theory.AlgebraicGroup
