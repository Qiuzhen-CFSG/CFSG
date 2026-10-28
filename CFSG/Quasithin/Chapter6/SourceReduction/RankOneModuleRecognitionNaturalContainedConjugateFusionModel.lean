module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionModelFixedLines
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusion

/-!
# The two local natural-action inputs for corank and fusion

Under genuine 6.1.1, naturality of its layer, and E.6.1, the full normalizer
of the layer normalizes L. The actual automizer construction therefore
supplies both the elementary-image rank bound and natural-offender fixed
lines. The elementary structure is exactly `h.layer_elementary`.

The final two applications discharge these local inputs in the published
corank and fusion deductions. The global-s identity and the earlier 6.1.9
normalizer factorization remain explicit, as required by those consumers.
Source: Aschbacher--Smith, 6.1.10--11, printed p.670.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

theorem elementaryActionRankBound_of_natural
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V)) :
    ElementaryActionRankBound (layer L V) n := by
  let := h.layer_elementary
  exact NaturalAction.elementaryActionRankBound h.n_gt_one hnatural
    (hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal))

theorem naturalOffenderFixedLines_of_natural
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V)) :
    letI := h.layer_elementary
    NaturalOffenderFixedLines (T : Subgroup G) L (layer L V) (ZS (T : Subgroup G) L V) := by
  let := h.layer_elementary
  exact NaturalAction.naturalOffenderFixedLines h.n_gt_one hnatural
    (hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal))
    T h.sylow_normalizes_L

theorem conjugateCorankFormula_of_natural_action
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n) :
    ConjugateCorankFormula (T : Subgroup G) (layer L V) n :=
  conjugateCorankFormula_of_rank_bound h hnatural hs
    (elementaryActionRankBound_of_natural h hnatural hE)

theorem mutualConjugateFusion_of_natural_action
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L V)) :
    MutualConjugateFusion (T : Subgroup G) (layer L V) (ZS (T : Subgroup G) L V) :=
  mutualConjugateFusion_of_local_inputs h hnatural hE hs
    (elementaryActionRankBound_of_natural h hnatural hE)
    (naturalOffenderFixedLines_of_natural h hnatural hE) hfactor
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
