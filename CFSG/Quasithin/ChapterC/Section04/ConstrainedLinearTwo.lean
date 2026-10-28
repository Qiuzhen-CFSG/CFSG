module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedRankOne
public import Theory.SpecificGroups.SL2.BinaryLinearComparison
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneBlocks
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Ranks
/-!
# Excluding the constrained binary SL2 source row

The literal star component has three-rank one. The full B.5 rank-one
classification leaves natural SL2, natural SL3, symmetric-five, and doubled
SL3 actions. Odd ranks and the order of SL3(2) exclude the SL3 markings;
the constrained A5 obstruction excludes symmetric-five. In the natural SL2
row, the original C.2.7 geometry makes the radical Sylow in KR, contradicting
the nontrivial action of the perfect span on the component quotient.

Source: Aschbacher–Smith C.4.4–6, printed pp.152–153, using B.5.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

theorem no_constrained_component_star_linear_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (F : BinaryField)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(2,F.Carrier)) : False := by
  let hi := h.constrained_source_input K hK hq hout hfK
  obtain ⟨hCJ,⟨c⟩⟩ := C27Source.star_moved_section_from_source hi
  let eC := (subgroupOfEquivOfLe hCJ).trans e
  have hr : primeRank 3 ((starImage (K.map H.subtype) R (K.map H.subtype)).subgroupOf
      (offenderSubgroup (starRepresentation (K.map H.subtype) R))) = 1 := by
    rw [primeRank_equiv 3 eC]
    exact Matrix.SL2.binary_threeRank_eq_one
  have hc := rankOneAction_of_source _ hr c.clause_one
  cases hc with
  | irreducible hir hf hirr hs hex =>
    cases hs with
    | linearTwo E hgen a ho hr =>
      have hsyl := (C27Source.rankOne_row_geometry_from_source hi hCJ c.sectionData E a hr ho).2.2
      exact h.no_constrained_component_of_radical_sylow K hK hq hout hfK hsyl
    | linearThree E hodd hgen a hr =>
      exact Matrix.SL2.binary_not_equiv_linear_three E.degree_pos E.card_eq
        (eC.symm.trans a.groupEquiv)
    | symmetricFive a ho hr =>
      exact h.no_constrained_component_star_alternating_five K hK hq hout hfK
        ((subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv)
  | doubleThree E ho hwhole a hoff hr =>
    exact Matrix.SL2.binary_not_equiv_linear_three E.degree_pos E.card_eq
      (eC.symm.trans a.groupEquiv)

end CFSG.Quasithin.ChapterC.HypothesisC28
