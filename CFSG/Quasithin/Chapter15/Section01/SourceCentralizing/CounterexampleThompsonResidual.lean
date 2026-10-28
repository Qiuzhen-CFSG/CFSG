module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Resolver
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.GlobalThompsonResidual
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.Normalization

/-!
# The counterexample contract for original 15.1.14

The actual 15.1.3 resolver excludes the Theorem E models and every
ordering-maximal natural orthogonal action before it uses 15.1.14. Retain
these hypotheses in a separate contract, leaving the general residual API
unchanged. The literal chosen origin includes the full module and the
complete proper-support data.

The equal-image and odd-or-twice-odd action cases are already proved.
Consequently two independent source obligations suffice: normalization on
the full module with strictly smaller Thompson image, and normalization on
the proper Omega support with Thompson image of order two. The assembly
below proves this reduction and applies it to the actual Resolver. These
two normalization obligations remain explicit; this is not a proof of
unconditional 15.1.14 or 15.1.3.

Source: Aschbacher--Smith, 15.1.13--14, printed pp.1090--1091, and the
counterexample assumption preceding 15.1.4, printed p.1087.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The residual input needed only after the two actual classification exits
have been excluded. It is deliberately distinct from the older general input. -/
abbrev SourceCounterexampleThompsonResidualInput
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
  (∀ N : Subgroup G, IsOrderingMaximal T N →
    ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
  SourceGlobalThompsonResidualInput hG T Mc

/-- The sufficient normalization contract, on precisely the same choices. -/
abbrev SourceCounterexampleThompsonNormalizationInput
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
  (∀ N : Subgroup G, IsOrderingMaximal T N →
    ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
  ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    ∀ W : Subgroup G, SourceChosenOrigin T M Mc W → PreparedChosenModule T M W →
      centralizer (centralInvolutions T : Set G) ≤ normalizer (thompsonFixed T W : Set G)

/-- The full-module obligation after removing the already proved image cases.
No action alternative, including the large-action alternatives, is omitted. -/
abbrev SourceFullThompsonImageGapInput
    (T : Sylow 2 G) (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
  (∀ N : Subgroup G, IsOrderingMaximal T N →
    ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
  ∀ (M : Subgroup G) (_hM : IsOrderingMaximal T M), M ≠ Mc →
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
    ∀ hp : PreparedChosenModule T M (localModule T M),
      4 ∣ Nat.card (internalActionImage M (localModule T M) hp.normalized) →
      ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M (localModule T M) hp.normalized).rangeRestrict <
        ((T : Subgroup G).subgroupOf M).map
          (actionHom M (localModule T M) hp.normalized).rangeRestrict →
      centralizer (centralInvolutions T : Set G) ≤
        normalizer (thompsonFixed T (localModule T M) : Set G)

/-- The remaining proper-support obligation. The full `Proper` witness keeps
the complement, fixed support, centralizer product and index-three intersection. -/
abbrev SourceProperThompsonImageTwoInput
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
  (∀ N : Subgroup G, IsOrderingMaximal T N →
    ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
  ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    ∀ U : Submodule (ZMod 2) (Additive (localModule T M)),
      SourceCases.Proper T M Mc (localModule T M)
        (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U →
      let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype
      ∀ hp : PreparedChosenModule T M W,
        Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M W hp.normalized).rangeRestrict) = 2 →
        centralizer (centralInvolutions T : Set G) ≤ normalizer (thompsonFixed T W : Set G)

/-- Both counterexample contracts use the literal ambient residual and centralizer. -/
theorem source_counterexample_thompson_residual_iff_normalization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G) (Mc : Subgroup G) :
    SourceCounterexampleThompsonResidualInput hG T Mc ↔
      SourceCounterexampleThompsonNormalizationInput hG T Mc := by
  constructor
  · intro h hmodel hno M hM hne hJ W hW hp
    exact (hp.thompsonFixed_residual_iff_normalizes hG T hM hJ).mp
      (h hmodel hno M hM hne hJ W hW hp)
  · intro h hmodel hno M hM hne hJ W hW hp
    exact hp.thompsonFixed_residual_of_normalizes hG T hM hJ
      (h hmodel hno M hM hne hJ W hW hp)

/-- The previously proved equal-image case fixes the chosen subgroup pointwise. -/
theorem PreparedChosenModule.centralizer_le_thompsonFixed_centralizer_of_image_eq
    (T : Sylow 2 G) {M W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hp : PreparedChosenModule T M W)
    (he : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M W hp.normalized).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M W hp.normalized).rangeRestrict) :
    centralizer (centralInvolutions T : Set G) ≤ centralizer (thompsonFixed T W : Set G) := by
  rw [hp.thompsonFixed_eq_seed_of_image_eq T hM he]
  exact centralizer_le inf_le_left

/-- Exact conditional assembly of the two remaining source branches.
The full-module and proper-support hypotheses are independent inputs. -/
theorem source_counterexample_thompson_normalization_of_image_gaps
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : SourceFullThompsonImageGapInput T Mc)
    (hproper : SourceProperThompsonImageTwoInput hG T Mc) :
    SourceCounterexampleThompsonNormalizationInput hG T Mc := by
  classical
  intro hmodel hno M hM hne hJ W hW hp
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  by_cases he : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M W hp.normalized).rangeRestrict =
    ((T : Subgroup G).subgroupOf M).map (actionHom M W hp.normalized).rangeRestrict
  · exact (hp.centralizer_le_thompsonFixed_centralizer_of_image_eq T hM he).trans
      (Subgroup.centralizer_le_normalizer _)
  have hfour : 4 ∣ Nat.card (internalActionImage M W hp.normalized) := by
    by_contra hc
    exact he (hp.thompson_image_eq_sylow_of_not_four_dvd hG T hempty hM hmany hJ hc)
  rcases hW with rfl | ⟨U,hU,rfl⟩
  · exact hfull hmodel hno M hM hne hJ hp hfour
      (lt_of_le_of_ne (map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ _))) he)
  · rcases source_proper_thompsonFixed_residual_or_image_two hG T hempty hM hmany hJ
      U hU hp with hres | htwo
    · exact (hp.thompsonFixed_residual_iff_normalizes hG T hM hJ).mp hres
    · exact hproper hmodel hno M hM hne hJ U hU hp htwo

/-- The literal residual input consumed by the counterexample Resolver. -/
theorem source_counterexample_thompson_residual_of_image_gaps
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : SourceFullThompsonImageGapInput T Mc)
    (hproper : SourceProperThompsonImageTwoInput hG T Mc) :
    SourceCounterexampleThompsonResidualInput hG T Mc :=
  (source_counterexample_thompson_residual_iff_normalization hG T Mc).mpr
    (source_counterexample_thompson_normalization_of_image_gaps hG T hempty hmany hfull hproper)

/-- Apply all clauses of 15.1.14 to the same source choice under the specialized input. -/
theorem source_lemma_15_1_14_of_counterexample_input
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc W : Subgroup G} (hM : IsOrderingMaximal T M) (hne : M ≠ Mc)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmodel : ¬ ClassificationModels.IsTheoremEModel G)
    (hno : ∀ N : Subgroup G, IsOrderingMaximal T N →
      ¬ Nonempty (NaturalOrthogonalAction N (localModule T N)))
    (hres : SourceCounterexampleThompsonResidualInput hG T Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceChosenOrigin T M Mc W → PreparedChosenModule T M W →
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
          (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T W : Set G) ∧
      M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
        normalizer (thompsonFixed T W : Set G) ∧
      normalizer (thompsonFixed T W : Set G) ≤ Mc ∧
      normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc := by
  intro hW hp
  have hr := hres hmodel hno M hM hne hJ W hW hp
  exact ⟨hr,hp.thompsonFixed_normalizers hG T hM hJ hu hr⟩

/-- The actual Resolver supplies both counterexample exclusions before applying
the specialized residual theorem to either the full module or the proper support. -/
theorem source_centralizing_resolver_of_counterexample_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hres : SourceCounterexampleThompsonResidualInput hG T Mc)
    (hlarge : SourceLargeChosenExclusionInput hG T Mc)
    (hsmall : SourceSmallChosenExclusionInput hG T Mc) :
    CentralizingResolver T Mc := by
  classical
  by_cases hmodel : ClassificationModels.IsTheoremEModel G
  · intro M hM hne hJ _ _ _ _
    exact Or.inl hmodel
  by_cases hn : ∃ N : Subgroup G, IsOrderingMaximal T N ∧
      Nonempty (NaturalOrthogonalAction N (localModule T N))
  · intro M hM hne hJ _ _ _ _
    exact Or.inr hn
  have hno : ∀ N : Subgroup G, IsOrderingMaximal T N →
      ¬ Nonempty (NaturalOrthogonalAction N (localModule T N)) :=
    fun N hN ho => hn ⟨N,hN,ho⟩
  exact source_centralizing_resolver_of_chosen_exclusions hG T hempty hu hmany hrank
    (hres hmodel hno) hlarge hsmall

/-- The pointwise 15.1.3 application retains the original singleton centralizer. -/
theorem source_lemma_15_1_3_of_counterexample_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hres : SourceCounterexampleThompsonResidualInput hG T Mc)
    (hlarge : SourceLargeChosenExclusionInput hG T Mc)
    (hsmall : SourceSmallChosenExclusionInput hG T Mc) :
    ClassificationModels.IsTheoremEModel G ∨
      ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)) :=
  source_lemma_15_1_3_of_branch_resolvers hG T hempty hu hmany hrank
    (source_centralizing_resolver_of_counterexample_residual hG T hempty hu hmany
      hrank hres hlarge hsmall)

/-- Literal final consumer of the two independent normalization branches.
The other source producers retain their original interfaces. -/
theorem source_lemma_15_1_3_of_thompson_image_gaps
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hfull : SourceFullThompsonImageGapInput T Mc)
    (hproper : SourceProperThompsonImageTwoInput hG T Mc)
    (hlarge : SourceLargeChosenExclusionInput hG T Mc)
    (hsmall : SourceSmallChosenExclusionInput hG T Mc) :
    ClassificationModels.IsTheoremEModel G ∨
      ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)) :=
  source_lemma_15_1_3_of_counterexample_residual hG T hempty hu hmany hrank
    (source_counterexample_thompson_residual_of_image_gaps hG T hempty hmany hfull hproper)
    hlarge hsmall

end CFSG.Quasithin.Chapter15.Section01
