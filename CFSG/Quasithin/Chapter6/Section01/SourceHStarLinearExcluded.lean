module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarE23
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.LinearGenerationObstruction

/-!
# Excluding the genuine single natural SL₂ row in the original H-star orbit

The noncentral omega orbit in Hypothesis 6.1.1 is reduced and moved by the
intrinsic Thompson subgroup. Apply the complete E.2.3 classification to its
literal centralizer quotient. The single natural SL₂ row gives a genuine
elementary Sylow lift and contradicts the original generation-parameter-one
hypothesis. The marked symmetric-five row and the two-factor rows remain
explicit for the source solvability assembly.

Source: Aschbacher--Smith 6.1.1 and 6.1.5, printed pp.665--669.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
open ChapterB ChapterB.QuasisimpleSource ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)

/-- The full original nonsolvable H-star classification after discharging the
single natural SL₂ alternative using `Hypothesis611.generation_one`. -/
theorem e23_nonsolvable_symmetric_or_pair
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hns : ¬ Group.IsSolvable H) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI : U.Normal := (RankOneGeneric.Input.hstar_omega_orbit_reduced
      (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).normal
    letI : IsElementaryAbelian 2 U := (RankOneGeneric.Input.hstar_omega_orbit_reduced
      (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let α : Representation (ZMod 2) (H ⧸ C) (Additive U) :=
      NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y : Subgroup (H ⧸ C) := offenderSubgroup α
    let σ : Representation (ZMod 2) Y (Additive U) := α.comp Y.subtype
    (IsQuasisimple (generalizedFitting Y) ∧
      ∃ c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        Nonempty (MarkedActionEquiv c.sectionData.action
          (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
      ∃ c : SourceInduction.SourceTwoFactorCase σ,
        SourceRankOneFactor σ c.first c.firstSpace ∧
          SourceRankOneFactor σ c.second c.secondSpace := by
  let hi := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := hi.hstar_omega_orbit_reduced hH'
  let := hU.normal
  let := hU.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple H :=
    Chapter3.sqtk_of_mem_H h.simpleQTKE hH'.1.1.1
  have hp := hi.hstar_minimal_parabolic hH'
  have hj := hi.hstar_thompson_moves_omega_orbit hH' hZH
  have hgen : ChapterE.IsEGenerated 1 H := by
    have hg := h.generation_one H hH
    simpa only [hg] using ChapterE.isEGenerated_generationParameter_of_pos
      (show 0 < ChapterE.generationParameter H by omega)
  rcases source_nonsolvable_natural_factors hsq S hp U hU hns hj with
    ⟨hqs, c, ⟨F, hF⟩ | hs⟩ | hpairs
  · exact (quasisimple_linear_not_isEGenerated_one S hp U hU hj _
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      hqs c.sectionData F hF hgen).elim
  · exact Or.inl ⟨hqs, c, hs⟩
  · exact Or.inr hpairs

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
