module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedChosen
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Natural

/-!
# Chief-action classification for the actual prepared chosen subgroup

The assembled source subgroup supplies its core containment and ratio-two
inputs. The source solvable action excludes dual FF, and the original
chosen normalizer supplies the QRC configuration and uniqueness. Applying
the genuine sharp-offender classification therefore gives the natural
alternatives on each noncentral chief factor of its literal H-span.

The larger-field alternatives remain to be excluded by the separate
Cartan argument. Source: Aschbacher--Smith 3.1.9(5) and15.1.12(3),
printed pp.577--578 and1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.chief_natural_alternatives
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
      ChapterB.ChiefNaturalAlternatives
        (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ∧
      subspaceCommutator (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ⊤
        (offenderSubgroup (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))) = ⊤ := by
  let := h.elementary
  let hqrc := chosenNormalizer_qrcHypotheses T hM.1.2 h.le_selected h.normalized h.seed_span hH
  have hu := source_chosenNormalizer_unique hG T hempty hM hJ h.nontrivial h.normalized h.seed_span
  obtain ⟨hq,hdual⟩ := source_chosen_equality_inputs hG T hempty hM hH hJ
    h.le_selected h.nontrivial h.normalized h.seed_span h.le_local h.quadratic_ratio
  exact hqrc.sqtk_chief_natural_alternatives hG hM.1.1 hu
    (hJ.trans (centralizer_le h.le_local)) h.nontrivial (h.inside_core H hH) hdual hq
end CFSG.Quasithin.Chapter15.Section01
