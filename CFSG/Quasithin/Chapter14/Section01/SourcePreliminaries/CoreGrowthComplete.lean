module
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.CoreGrowth
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.ExceptionalCentralizer
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.CubicCentralizer

/-!
# Original intersection-core growth with the exceptional branch

Characteristic radical control either contains the generalized-Fitting
preimage or contains the centralizer of the central seed through the full
exceptional cubic product. In the latter case its maximal local overgroup is
unique. Applying this dichotomy to the intersection of distinct maximal
locals excludes equality of their two-cores. The equality R=O₂(H) required
by the exceptional argument is supplied by that intersection itself.

Source: Aschbacher–Smith 14.1.13–14, printed p.979.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries
open Chapter15.Section03 Chapter15.Section03.InitialSource ChapterC.Section02Source
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem intersection_core_ne_local_core_of_radical_alternative
    (T : Sylow 2 G)
    {M N : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hcontrol : ∀ (R H : Subgroup N), IsPRadical 2 R →
      R ≤ (T.subtype hN.2 : Subgroup N) →
      H.pCoreIn 2 = R →
      (T.subtype hN.2 : Subgroup N) ≤ H →
      R.characteristicNormalizerClosure ≤ H →
      (generalizedFitting (N ⧸ pCore 2 N)).comap (QuotientGroup.mk' (pCore 2 N)) ≤ H ∨
      maximalTwoLocalOvergroups (H.map N.subtype) = {N})
    (hne : M ≠ N) :
    (M ⊓ N).pCoreIn 2 ≠ M.pCoreIn 2 := by
  intro he
  let R := M.pCoreIn 2
  have hRN : R ≤ N := by
    change M.pCoreIn 2 ≤ N
    rw [←he]
    exact (pCoreIn_le 2 (M ⊓ N)).trans inf_le_right
  have hRT : R ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hM.2] using
      pCoreIn_le_sylow M (T.subtype hM.2)
  have hnorm : normalizer (R.subgroupOf N : Set N) = M.subgroupOf N := by
    rw [←subgroupOf_normalizer_eq hRN,maximalTwoLocal_normalizer_core hM.1]
  have hr : IsPRadical 2 (R.subgroupOf N) := by
    refine ⟨?_,?_⟩
    · intro hz
      have hh := congrArg (map N.subtype) hz
      rw [map_subgroupOf_eq_of_le hRN,Subgroup.map_bot] at hh
      exact maximalTwoLocal_core_ne_bot hM.1 hh
    · change (normalizer (R.subgroupOf N : Set N)).pCoreIn 2 = R.subgroupOf N
      apply map_injective N.subtype_injective
      rw [map_pCoreIn_of_injective 2 _ _ N.subtype_injective,hnorm,
        subgroupOf_map_subtype,he,map_subgroupOf_eq_of_le hRN]
  have hcpu : (R.subgroupOf N).characteristicNormalizerClosure ≤ M.subgroupOf N :=
    characteristicNormalizerClosure_subgroupOf_le hRN
      (maximalTwoLocal_characteristicNormalizer_core hM.1).le
  have hRH : (M.subgroupOf N).pCoreIn 2 = R.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ _ N.subtype_injective,
      subgroupOf_map_subtype,he,map_subgroupOf_eq_of_le hRN]
  have halt := hcontrol (R.subgroupOf N) (M.subgroupOf N) hr
    (comap_mono hRT) hRH (comap_mono hM.2) hcpu
  have hfit : (generalizedFitting (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N)) ≤ M.subgroupOf N := by
    rcases halt with hfit | hunique
    · exact hfit
    · have hMM : M ∈ maximalTwoLocalOvergroups ((M.subgroupOf N).map N.subtype) := by
        refine ⟨hM.1,?_⟩
        rw [subgroupOf_map_subtype]
        exact inf_le_left
      exact (hne (Set.mem_singleton_iff.mp (hunique ▸ hMM))).elim
  have hfitM : ChapterA.Section04.twoGeneralizedFittingPreimage N ≤ M := by
    rintro x ⟨y,hy,rfl⟩
    exact hfit hy
  have hfitN : ChapterA.Section04.twoGeneralizedFittingPreimage N ≤ N := map_subtype_le _
  have ha : ChapterA.Section04.IntersectionAlternative
      (ChapterA.Section04.twoCoreQuotientImage N (ChapterA.Section04.twoGeneralizedFittingPreimage N)) := by
    rw [ChapterA.Section04.twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl,?_,?_⟩
    · exact (inferInstance : ((generalizedFitting (N ⧸ pCore 2 N)).subgroupOf
        (generalizedFitting (N ⧸ pCore 2 N))).Normal).isSubnormal
    · exact (closure_le _).mpr (fun x hx => hx.1.1)
  have hcores := ChapterA.Section04.lemma_A_4_4_1 N M (ChapterA.Section04.twoGeneralizedFittingPreimage N)
    (ChapterA.Section04.twoCore_le_fittingPreimage N) (le_inf hfitN hfitM) ha
  rw [inf_comm N M,he] at hcores
  apply hne
  rw [←maximalTwoLocal_normalizer_core hM.1,←hcores,maximalTwoLocal_normalizer_core hN.1]


/-- Original14.1.13 with its actual radical-core and Sylow containment hypotheses. -/
theorem source_radical_control_alternative
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (R H : Subgroup M) (hr : IsPRadical 2 R)
    (hRT : R ≤ (T.subtype hM.2 : Subgroup M))
    (hcore : H.pCoreIn 2 = R)
    (hTH : (T.subtype hM.2 : Subgroup M) ≤ H)
    (hcontrol : R.characteristicNormalizerClosure ≤ H) :
    (generalizedFitting (M ⧸ pCore 2 M)).comap (QuotientGroup.mk' (pCore 2 M)) ≤ H ∨
      maximalTwoLocalOvergroups (H.map M.subtype) = {M} := by
  by_cases hf : (generalizedFitting (M ⧸ pCore 2 M)).comap
      (QuotientGroup.mk' (pCore 2 M)) ≤ H
  · exact Or.inl hf
  right
  obtain ⟨he,_,N,hN,hm,hNH⟩ := source_exceptional_centralizer_control
    hG T hempty hM hu hmany R H hr hRT hcontrol hcore hf
  let : N.Normal := hN
  have hCH : centralizer (centralInvolutions T : Set G) ≤ H.map M.subtype :=
    (source_cubic_orbit_centralizer_control T hM.2 hu he N hm).trans
      (map_mono (sup_le hNH hTH))
  ext L
  constructor
  · intro hL
    have hLC : L ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      ⟨hL.1,hCH.trans hL.2⟩
    rw [hu,Set.mem_singleton_iff] at hLC
    exact Set.mem_singleton_iff.mpr (hLC.trans he.symm)
  · rintro rfl
    exact ⟨hM.1,map_subtype_le _⟩

/-- Original14.1.14, including the exceptional centralizer-partner branch. -/
theorem intersection_core_ne_local_core_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M N Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : M ≠ N) :
    (M ⊓ N).pCoreIn 2 ≠ M.pCoreIn 2 :=
  intersection_core_ne_local_core_of_radical_alternative T hM hN
    (source_radical_control_alternative hG T hempty hN hu hmany) hne

end CFSG.Quasithin.Chapter14.SourcePreliminaries
