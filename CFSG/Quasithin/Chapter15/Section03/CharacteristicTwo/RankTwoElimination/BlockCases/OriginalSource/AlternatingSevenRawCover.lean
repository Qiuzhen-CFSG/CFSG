module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenIntrinsic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenRaw
public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
/-!
# The remaining central cover in the raw seven-point row

The literal B.5 marked action identifies the star component with A₇. The
core-to-star map is a perfect central cover, so its trivial two-core leaves
only A₇ and the genuine triple cover. In the ordinary case the actual
source offender makes R* odd in S₇; its normalizer has three-rank at most
one, contradicting the image of Y₊. Thus a raw symmetric-seven row forces
the triple cover and a kernel of order three. All six B.5 clauses remain
in the final consumer's actual source input.

This is a reduction of the raw row, not its final exclusion. It isolates
the cubic-center action needed next. Source: Aschbacher–Smith B.5.1,
C.2.7(1–2),15.3.17–21, pp.99–103,145–146,1126–1127; GLS3 5.2.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
theorem coreToStar_alternatingSeven_alternatives
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (e : starImage c.L d.R c.L ≃* alternatingGroup (Fin 7)) :
    Nonempty ((c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 7)) ∨
      (Nat.card (coreToStar hR).ker = 3 ∧
        Nonempty ((c.L ⧸ pCore 2 c.L) ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : Nontrivial (starImage c.L d.R c.L) := e.symm.injective.nontrivial
  have hne : starImage c.L d.R c.L ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  let f := coreStarCover hR c.core_quotient_quasisimple hne
  have hz : center (starImage c.L d.R c.L) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center (alternatingGroup (Fin 7)) := (centerCongr e ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hk : (coreToStar hR).ker = center (c.L ⧸ pCore 2 c.L) := by
    have hh := f.comap_center
    rwa [hz,MonoidHom.comap_bot] at hh
  let q : ((c.L ⧸ pCore 2 c.L) ⧸ center (c.L ⧸ pCore 2 c.L)) ≃*
      alternatingGroup (Fin 7) :=
    f.quotientCenterEquiv.trans
      (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e)
  let : IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
  have ho : Odd (Nat.card (center (c.L ⧸ pCore 2 c.L))) :=
    Nat.not_even_iff_odd.mp (fun hh =>
      PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
        (pCore_quotient_pCore_eq_bot 2) _ le_rfl (even_iff_two_dvd.mp hh))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 7 (by decide) q ho with hc | ⟨_,hc⟩
  · exact Or.inl ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 7 q hc⟩
  · exact Or.inr ⟨hk ▸ hc,GLS3.Chapter5.OddCentralCovers.triple_seven_equiv q hc⟩

private theorem no_alternatingSeven_quotient_of_radical_rank
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (hrank : primeRank 3 d.Yplus = 2) (hYL : d.Yplus ≤ c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 7))
    (fperm : StarQuotient c.L d.R →* Equiv.Perm (Fin 7))
    (hfi : Function.Injective fperm)
    (hne : starImage c.L d.R c.L ≠ ⊥)
    (hsmall : primeRank 3 (normalizer
      ((starImage c.L d.R d.R).map fperm :
        Set (Equiv.Perm (Fin 7)))) ≤ 1) : False := by
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


/-- The raw natural row contradicts an ordinary A7 component quotient. -/
theorem no_raw_alternatingSeven_of_core_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (eq : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 7)) :
    let C := starImage c.L d.R c.L
    let J := Representation.BinaryOffender.offenderSubgroup (starRepresentation c.L d.R)
    ∀ (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (alternatingNatural 7) → False := by
  intro C J s es
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL := yplus_le_of_alternatingSeven_quotient d c h11.theta_eq.symm hrI eq
  obtain ⟨f,hfi,hfcomp⟩ := alternatingSeven_star_embedding h eq
  have houter := alternatingSeven_raw_radical_not_le_component h s es
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
  have hne := starImage_ne_bot_of_bound h.normalizes h.quasisimple hk.upper
  exact no_alternatingSeven_quotient_of_radical_rank d c h.normalizes
    (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) hYL eq f hfi hne hsmall

private noncomputable def marked_seven_restriction
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {H L : Subgroup D}
    (e : MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin 7))
      (alternatingGroup (Fin 7))) :
    ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7) where
  groupEquiv := e.subgroupEquiv
  linearEquiv := e.action.linearEquiv
  intertwines g v := by
    have he := e.action.intertwines ⟨g,e.contained g.property⟩ v
    rw [e.compatible] at he
    exact he

/-- A literal B.5 symmetric-seven row leaves only the nontrivial triple cover.
All six source clauses and the actual moved section remain in the input. -/
theorem raw_symmetricSeven_core_triple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I) :
    let C := starImage c.L d.R c.L
    let J := Representation.BinaryOffender.offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (qsrc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      MarkedActionEquiv qsrc.sectionData.action
        (Representation.BinaryOffender.offenderSubgroup qsrc.sectionData.action)
        (C.subgroupOf J) (BinaryPermutation.naturalRepresentation (Fin 7))
        (alternatingGroup (Fin 7)) →
      ∃ hR : d.R ≤ normalizer (c.L : Set G),
        Nat.card (coreToStar hR).ker = 3 ∧
        Nonempty ((c.L ⧸ pCore 2 c.L) ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) := by
  intro C J hCJ qsrc e
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  let eC : C ≃* alternatingGroup (Fin 7) :=
    (subgroupOfEquivOfLe hCJ).symm.trans e.subgroupEquiv
  let es := marked_seven_restriction qsrc.sectionData.action e
  rcases coreToStar_alternatingSeven_alternatives d c h.normalizes eC with hh | hh
  · obtain ⟨eq⟩ := hh
    exact (no_raw_alternatingSeven_of_core_quotient hG d hempty hM hu hmany hI htwo hf c
      eq qsrc.sectionData es).elim
  · exact ⟨h.normalizes,hh⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
