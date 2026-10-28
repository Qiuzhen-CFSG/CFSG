module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedChiefActions
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.ActorQuotient
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SmallCentralization

/-!
# The small natural actions for the actual prepared chosen module

The chosen source module supplies the residual-centralizer hypothesis that
excludes larger fields. Its literal H-span therefore has only the four
small natural chief actions. The kernel quotient corollary records their
S₃, S₃≀C₂, S₅, and S₅≀C₂ names; the first theorem retains whole action
coordinates rather than just group isomorphism types.

Source: Aschbacher–Smith, original 15.1.12(3), using 3.1.9(5), printed
pp.1090 and577–578. The final theorem supplies original 15.1.12(4) for this same chosen module.
The paired Thompson-image equalities are separate.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.chief_small_whole_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    letI := h.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.chief_data hG T hempty hM hJ H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.inside_core H hH).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      ChapterB.ChiefSmallWholeAction
        (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) := by
  let := h.elementary
  let hqrc := chosenNormalizer_qrcHypotheses T hM.1.2 h.le_selected h.normalized h.seed_span hH
  have hu := source_chosenNormalizer_unique hG T hempty hM hJ h.nontrivial h.normalized h.seed_span
  obtain ⟨hq,hdual⟩ := source_chosen_equality_inputs hG T hempty hM hH hJ
    h.le_selected h.nontrivial h.normalized h.seed_span h.le_local h.quadratic_ratio
  exact hqrc.sqtk_chief_small_whole_action hG hM.1.1 hu
    (hJ.trans (centralizer_le h.le_local)) h.nontrivial (h.inside_core H hH) hdual (h.intersection_residual H hH) hq

theorem PreparedChosenModule.chief_small_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    letI := h.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.chief_data hG T hempty hM hJ H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.inside_core H hH).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      ChapterB.ChiefSmallActor (H ⧸ (actionHom (s.factorRepresentation i)).ker) := by
  let := h.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hG T hempty hM hJ H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H hH).trans (twoCore_le H)))
  have hc := h.chief_small_whole_action hG T hempty hM hJ hH
  dsimp only
  intro s i hi
  exact (hc s i hi).quotient_actor

theorem PreparedChosenModule.thompson_omega_centralizes_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) ≤
      centralizer ((pResidual 2 H).map H.subtype : Set G) := by
  let := h.elementary
  let hqrc := chosenNormalizer_qrcHypotheses T hM.1.2 h.le_selected h.normalized h.seed_span hH
  have hu := source_chosenNormalizer_unique hG T hempty hM hJ h.nontrivial h.normalized h.seed_span
  obtain ⟨hq,hdual⟩ := source_chosen_equality_inputs hG T hempty hM hH hJ
    h.le_selected h.nontrivial h.normalized h.seed_span h.le_local h.quadratic_ratio
  exact hqrc.sqtk_thompson_omega_centralizes_residual hG hM.1.1 hu
    (hJ.trans (centralizer_le h.le_local)) h.nontrivial (h.inside_core H hH) hdual hq
    (h.intersection_residual H hH)

end CFSG.Quasithin.Chapter15.Section01
