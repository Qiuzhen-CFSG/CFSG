module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Classification.RankOneFactors
public import CFSG.Quasithin.Chapter3.Section01.E23Input

/-!
# Natural rank-one factor selection on the original qrc omega orbit

The genuine Chapter 3 source construction provides reduction, minimal
parabolicity and Thompson movement for the literal omega-center orbit in H.
Apply the full earlier classification and the proved source factor exclusions. All
centralizer quotients and subgroup restrictions remain those of the source.

Source: Aschbacher–Smith, 3.1.7 and E.2.3, pp.575–576 and 216–217.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The original nonsolvable source has quasisimple B.5.1 data or two actual natural rank-one factors. -/
theorem QrcHypotheses.e23_nonsolvable_rankOne_factors_or_quasisimple_of_earlier
    (hA : ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput.{u}
      KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hs : ¬ Group.IsSolvable H)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let hU := h.sylowOmega_reduced (hG.evenCharacteristic T)
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup ρ
    let σ := ρ.comp Y.subtype
    (IsQuasisimple (generalizedFitting Y) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ
        (generalizedFitting Y))) ∨
      ∃ c : ChapterB.SourceInduction.SourceTwoFactorCase σ,
        ChapterB.SourceRankOneFactor σ c.first c.firstSpace ∧
          ChapterB.SourceRankOneFactor σ c.second c.secondSpace := by
  obtain ⟨hsq,_,hp,hU,hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  exact ChapterE.ThompsonAction.source_nonsolvable_rankOne_factors_or_quasisimple_of_earlier
    hA h36 h4 hsq _ hp _ hU hs hj

end CFSG.Quasithin.Chapter3
