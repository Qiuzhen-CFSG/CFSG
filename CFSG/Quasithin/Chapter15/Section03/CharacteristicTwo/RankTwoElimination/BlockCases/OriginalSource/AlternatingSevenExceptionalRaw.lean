module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenRawTriple
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SplitMovedCard
/-!
# The first choice in the original exceptional A₇ moved row

The actual four-dimensional A₇ moved section splits from the fixed space,
for either dual orientation. Its original moved subgroup therefore has
order sixteen. In the first choice V=[V,Y₊], the selected seed lies in
that subgroup and has the same order. Thus L normalizes V, contradicting
the original normalizer bound. Both A₇ and 3·A₇ core quotients are retained;
no short-block reconstruction or two-group star-kernel claim is used.

The final consumer retains all six actual B.5 clauses and uses exactly the
irreducible/alternatingSeven constructor fields. The second source choice
is not discharged by this module.

Source: Aschbacher–Smith B.5.1,C.2.7 and15.3.21, pp.99–103,145–147,1127.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- In the first local choice, a split four-dimensional moved section fills
the original sixteen and forces L into its forbidden normalizer. -/
theorem raw_split_four_first_choice_false
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G)) (hYL : d.Yplus ≤ c.L)
    (hVW : d.V ≤ (starV c.L d.R).map (c.L ⊔ d.R : Subgroup G).subtype)
    (hNV : normalizer (d.V : Set G) ≤ d.M)
    (hcomm : d.V = ⁅d.V,d.Yplus⁆) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      IsCompl s.space.toSubmodule
        (fixedSpace ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)) →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 → False := by
  intro C J hCJ s hc hd
  let N := c.L ⊔ d.R
  let K := c.L.subgroupOf N
  let H := d.Yplus.subgroupOf N
  let V := d.V.subgroupOf N
  let U := starV c.L d.R
  have hLJ : c.L ≤ N := le_sup_left
  have hYJ : d.Yplus ≤ N := hYL.trans hLJ
  have hVJ : d.V ≤ N := hVW.trans (map_subtype_le _)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le c.L.le_normalizer hR)
  have hVstar : V ≤ U := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hVW hx
    exact (show y = x from Subtype.ext he) ▸ hy
  have hcomm' : V = ⁅V,H⁆ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVJ,map_subgroupOf_eq_of_le hYJ]
    exact hcomm
  have hVU : V ≤ ⁅U,K⁆ := by
    rw [hcomm']
    exact commutator_mono hVstar (comap_mono hYL)
  have hcard : Nat.card V = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVJ).toEquiv).trans d.action.card_vector
  have hcardU : Nat.card (⁅U,K⁆ : Subgroup N) = 16 := by
    simpa using ChapterC.C27Source.star_moved_commutator_card c.L d.R hCJ s hc 4 hd
  have heq : V = ⁅U,K⁆ := eq_of_le_of_card_ge hVU (by omega)
  have hn : K ≤ normalizer (V : Set N) := by
    rw [heq, normalizer_eq_top]
    exact le_top
  have hnG : c.L ≤ normalizer (d.V : Set G) := by
    have hh := (map_mono hn).trans (V.le_normalizer_map N.subtype)
    rw [map_subgroupOf_eq_of_le hLJ,map_subgroupOf_eq_of_le hVJ] at hh
    exact hh
  exact c.outside (hnG.trans hNV)

/-- The complete original context excludes the first choice for the actual
four-dimensional A₇ moved row, for either possible core cover. -/
theorem source_15_3_21_raw_exceptionalSeven_first_choice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hfirst : d.Yplus = d.Y) :
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
  have hYL : d.Yplus ≤ c.L := by
    rcases coreToStar_alternatingSeven_alternatives d c h.normalizes eC with hh | hh
    · obtain ⟨eq⟩ := hh
      exact yplus_le_of_alternatingSeven_quotient d c h11.theta_eq.symm hrI eq
    · obtain ⟨_,⟨eq⟩⟩ := hh
      exact yplus_le_of_tripleSeven_quotient d c h11.theta_eq.symm hrI eq
  have hVW := RankTwoElimination.OriginalSource.component_seed_le_starV d h htwo.2.2.2.2.1
  have hNV := InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1
  have hcomm : d.V = ⁅d.V,d.Yplus⁆ := by
    obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
      hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
    obtain ⟨hi,_,_,_⟩ := source_lemma_15_3_7_of_orthogonal_action
      hG d.T hempty d.action hM hu hmany hne
    rw [hfirst]
    exact (d.action.commutator_eq_of_residual_image d.Y
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) hi).symm
  exact raw_split_four_first_choice_false d c h.normalizes hYL hVW hNV.ge hcomm
    hCJ qsrc.sectionData (ExtensionConsequences.alternatingSeven_isCompl qsrc.sectionData hi e hd) hd

/-- Literal constructor consumer: the assumptions after the complete B.5
source record are precisely its irreducible/alternatingSeven row fields.
The legacy catalogue is used only internally for this identical A₇ row. -/
theorem source_15_3_21_raw_exceptionalSeven_first_choice_of_row
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hfirst : d.Yplus = d.Y) :
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
  exact source_15_3_21_raw_exceptionalSeven_first_choice
    hG d hempty hM hu hmany hI htwo hf c hfirst hCJ qsrc hi e hd

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
