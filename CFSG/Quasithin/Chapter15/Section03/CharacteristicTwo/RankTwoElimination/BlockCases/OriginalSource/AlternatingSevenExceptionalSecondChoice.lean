module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenExceptionalInner
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenExceptionalFixed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenSecondChoiceCenter

/-!
# The second choice in the original exceptional A₇ moved row

The literal B.5 exceptional four-space identifies the star component with A₇.
Its perfect core cover is either A₇ or the genuine triple cover. In the ordinary
case the actual rank-two Y₊ image has no nonzero fixed vector on the faithful
four-space. The split moved section consequently makes the selected plane
L-fixed, contradicting its normalizer bound. In the triple-cover case every
actual S actor is inner on the core quotient, by the moved-action intertwiner
and perfect-cover uniqueness. It fixes the cubic center, contrary to the
original second-choice Y₊S/O₂(Y₊S) ≅ S₃×S₃ quotient.

All six B.5 source clauses and all irreducible/alternatingSeven constructor
fields remain in the final consumer. Earlier original-source producers supply
the seed, residual rank, component containment and second-choice quotient.
There is no assumption that the star kernel is a two-group.

Source: Aschbacher–Smith B.5.1,C.2.7 and15.3.21, pp.99–103,145–147,1127.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- Both genuine core-cover alternatives are excluded in the original second choice. -/
theorem source_15_3_21_raw_exceptionalSeven_second_choice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hsecond : OutsideStructure.SecondChoice d) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (qsrc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (_hi : ExtensionConsequences.IrreducibleAlternative (C.subgroupOf J) qsrc.sectionData)
      (_e : (C.subgroupOf J) ≃* alternatingGroup (Fin 7)),
      Module.finrank (ZMod 2)
        (qsrc.sectionData.space.toSubmodule ⧸ qsrc.sectionData.central.toSubmodule) = 4 → False := by
  intro C J hCJ qsrc hi e hd
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  let eC : C ≃* alternatingGroup (Fin 7) := (subgroupOfEquivOfLe hCJ).symm.trans e
  rcases coreToStar_alternatingSeven_alternatives d c h.normalizes eC with hh | hh
  · obtain ⟨eq⟩ := hh
    have hYL := yplus_le_of_alternatingSeven_quotient d c h11.theta_eq.symm hrI eq
    have hz : center (c.L ⧸ pCore 2 c.L) = ⊥ := by
      apply bot_unique
      intro x hx
      have he : eq x ∈ center (alternatingGroup (Fin 7)) := (centerCongr eq ⟨x,hx⟩).property
      rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
      exact eq.map_eq_one_iff.mp he
    have hne : C ≠ ⊥ := by
      let : Nontrivial C := eC.symm.injective.nontrivial
      exact (nontrivial_iff_ne_bot _).mp inferInstance
    have hinj : Function.Injective (coreToStar h.normalizes) :=
      (MonoidHom.ker_eq_bot_iff _).mp
        (bot_unique (hz ▸ coreToStar_ker_le_center h.normalizes c.core_quotient_quasisimple hne))
    have hVW := RankTwoElimination.OriginalSource.component_seed_le_starV d h htwo.2.2.2.2.1
    have hYC : d.Yplus ≤ centralizer (d.V₁ : Set G) := by
      rw [hsecond.2]
      exact (map_subtype_le _).trans inf_le_right
    exact raw_split_four_second_choice_false d c h.normalizes hYL
      (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) hinj hVW
      (h11.second_choice hsecond).2.1 hYC hCJ qsrc.sectionData
      (ExtensionConsequences.alternatingSeven_isCompl qsrc.sectionData hi e hd) hi.faithful hd
  · obtain ⟨_,⟨eq⟩⟩ := hh
    have hYL := yplus_le_of_tripleSeven_quotient d c h11.theta_eq.symm hrI eq
    have hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3 :=
      (Nat.card_congr (centerCongr eq).toEquiv).trans
        GLS3.Chapter5.OddCentralCovers.tripleSeven_center_card
    obtain ⟨hn,hinner⟩ := source_raw_exceptionalSeven_sylow_inner
      hG d hempty hM hu hmany hI htwo hf c hCJ qsrc.sectionData hi.faithful e hd
    exact source_rankTwo_secondChoice_cubic_center_false_of_inner
      hG d hempty hM hu hmany hI htwo hsecond c hYL hc hn hinner

/-- Literal B.5 constructor consumer, retaining the complete source record. -/
theorem source_15_3_21_raw_exceptionalSeven_second_choice_of_row
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hsecond : OutsideStructure.SecondChoice d) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    let ρ := (starRepresentation c.L d.R).comp J.subtype
    let C0 := C.subgroupOf J
    ∀ (_hCJ : C ≤ J)
      (qsrc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C0),
    let s := qsrc.sectionData
    ∀ (_hplus : IsIrrPlus ρ C0 s.space.toSubmodule)
      (_hfaith : Function.Injective s.action)
      (_hirr : IsIrreducible (s.action.comp C0.subtype))
      (_hgen : offenderSubgroup s.action = C0) (_hwhole : C0 = ⊤)
      (e : C0 ≃* alternatingGroup (Fin 7))
      (_hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4)
      (_hoff : ∀ A, IsBestOffender s.action A → ∃ g : alternatingGroup (Fin 7),
        ((A.subgroupOf C0).map ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom)) =
        (Subgroup.closure {ChapterB.Offenders.kleinFirst 7 (by decide),
          ChapterB.Offenders.kleinSecond 7 (by decide)}).map
          (MulAut.conj (g : Equiv.Perm (Fin 7))).toMonoidHom)
      (_hq : quadraticRatio s.action = 1), False := by
  intro C J ρ C0 hCJ qsrc s hplus hfaith hirr hgen hwhole e hd hoff hq
  have hi : ExtensionConsequences.IrreducibleAlternative C0 s :=
    ⟨hplus,hfaith,hirr,.alternatingSeven hgen hwhole e hd hoff hq,Or.inl hwhole⟩
  exact source_15_3_21_raw_exceptionalSeven_second_choice
    hG d hempty hM hu hmany hI htwo hf c hsecond hCJ qsrc hi e hd

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
