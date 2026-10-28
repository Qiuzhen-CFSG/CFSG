module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSeven
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenEmbedding
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import Theory.SpecificGroups.SymmetricSeven.OddNormalizers
/-!
# The ordinary A₇ exclusion in original15.3.21

The source's actual offender forces R* to contain an odd permutation in the
faithful seven-letter action. Every such two-subgroup has normalizer of
three-rank at most one. The original Yplus lies in the component, normalizes
R=O₂(Yplus S), and maps with a two-group kernel into this normalizer. Its
three-rank two is the required contradiction.

This closes the ordinary A₇ branch from the original local hypotheses,
without any transposition, radical-type or symmetric-model premise.
Source: Aschbacher–Smith C.2.7(1–2),15.3.17 and15.3.21, pp.145–146,1126–1127.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
theorem no_alternatingSeven_of_injective_radical_normalizer_rank
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (hrank : primeRank 3 d.Yplus = 2) (hYL : d.Yplus ≤ c.L)
    (hblock : ChapterC.IsAlternatingBlock c.L 7)
    (fperm : StarQuotient c.L d.R →* Equiv.Perm (Fin 7))
    (hfi : Function.Injective fperm)
    (hne : starImage c.L d.R c.L ≠ ⊥)
    (hsmall : primeRank 3 (normalizer
      ((starImage c.L d.R d.R).map fperm :
        Set (Equiv.Perm (Fin 7)))) ≤ 1) : False := by
  obtain ⟨e⟩ := hblock.2.2.quotient_iso
  have hz : center (c.L ⧸ pCore 2 c.L) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    apply mem_bot.mpr
    have he : e x ∈ center (alternatingGroup (Fin 7)) := (centerCongr e ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  let a := coreStarEquivOfCenterEqBot hR c.core_quotient_quasisimple hne hz
  let J := c.L ⊔ d.R
  let q := QuotientGroup.mk' (starKernel c.L d.R)
  have hYN : d.Yplus ≤ normalizer (d.R : Set G) :=
    (le_sup_left : d.Yplus ≤ d.Yplus ⊔ d.S).trans
      ((d.Yplus ⊔ d.S).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (d.Yplus ⊔ d.S)
          (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))))
  have hYNJ : d.Yplus.subgroupOf J ≤ normalizer (d.R.subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq (show d.R ≤ J from le_sup_right)]
    exact comap_mono hYN
  have hYNstar : starImage c.L d.R d.Yplus ≤
      normalizer (starImage c.L d.R d.R : Set (StarQuotient c.L d.R)) :=
    (map_mono hYNJ).trans ((d.R.subgroupOf J).le_normalizer_map q)
  let B := (starImage c.L d.R d.R).map fperm
  have hYNperm : (starImage c.L d.R d.Yplus).map fperm ≤
      normalizer (B : Set (Equiv.Perm (Fin 7))) :=
    (map_mono hYNstar).trans ((starImage c.L d.R d.R).le_normalizer_map fperm)
  let f : d.Yplus →* Equiv.Perm (Fin 7) := fperm.comp
    ((starImage c.L d.R c.L).subtype.comp ((toStarImage c.L d.R).comp (inclusion hYL)))
  have hf (y : d.Yplus) : f y ∈ normalizer (B : Set (Equiv.Perm (Fin 7))) := by
    apply hYNperm
    apply mem_map_of_mem
    exact mem_map_of_mem q y.property
  let g : d.Yplus →* normalizer (B : Set (Equiv.Perm (Fin 7))) := f.codRestrict _ hf
  have hk : IsPGroup 2 g.ker := by
    let j : g.ker →* pCore 2 c.L :=
      ((inclusion hYL).comp g.ker.subtype).codRestrict _ (by
        intro y
        apply (QuotientGroup.eq_one_iff _).mp
        apply a.injective
        change toStarImage c.L d.R (inclusion hYL y.val) = 1
        apply Subtype.ext
        apply hfi
        simp only [Subgroup.coe_one,map_one]
        have hh : f y.val = 1 := congrArg Subtype.val (show g y.val = 1 from y.property)
        exact hh)
    exact pCore_isPGroup.of_injective j (by
      intro x y hh
      apply Subtype.ext
      apply (inclusion_injective hYL)
      exact congrArg Subtype.val hh)
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card g.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hb := (primeRank_le_of_coprime_ker 3 g hcop).trans hsmall
  omega


/-- Ordinary A7 is excluded from the original rank-two source context.
The actual C.2.7 offender forces an odd radical image, whose normalizer cannot
contain the image of Yplus of three-rank two. All marking premises are discharged. -/
theorem source_15_3_21_alternatingSeven
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hb : ChapterC.IsAlternatingBlock c.L 7) : False := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  obtain ⟨eq⟩ := hb.2.2.quotient_iso
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL := yplus_le_of_alternatingSeven_quotient d c h11.theta_eq.symm hrI eq
  obtain ⟨f,hfi,hfcomp⟩ := alternatingSeven_star_embedding h eq
  have houter := alternatingSeven_radical_not_le_component h hb
  let B := (starImage c.L d.R d.R).map f
  have hodd : ¬ B ≤ alternatingGroup (Fin 7) := by
    intro hh
    apply houter
    apply (map_le_map_iff_of_injective hfi).mp
    rw [hfcomp]
    exact hh
  have hp : IsPGroup 2 B := by
    have hR : IsPGroup 2 d.R := by
      have hh := h.setup.radical.isPGroup.map I.subtype
      rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
    exact (hR.comap_subtype.map _).map f
  have hsmall := Theory.SpecificGroups.SymmetricSeven.OddNormalizers.normalizer_rank B hp hodd
  have hk := (ChapterC.C27Source.kernel_offender_from_source h).1
  have hne := Chapter1.RadicalExclusions.ModelReduction.FullSieve.starImage_ne_bot_of_bound
    h.normalizes h.quasisimple hk.upper
  exact no_alternatingSeven_of_injective_radical_normalizer_rank d c h.normalizes
    (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) hYL hb f hfi hne hsmall
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
