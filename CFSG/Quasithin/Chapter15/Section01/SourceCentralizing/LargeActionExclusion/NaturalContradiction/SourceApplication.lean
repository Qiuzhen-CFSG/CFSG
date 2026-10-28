module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction

/-!
# Applying the parabolic contradiction to the original chosen component

The common construction obligation selects the parabolics and the rank-two
input together. This prevents two independently chosen parabolic triples
from being silently identified. The theorem applies the conditional
contradiction to the literal component and moving element recognized by
15.1.26--28. Discharging the construction obligation and C.1.34 remains
necessary before claiming the source exclusion.

Source: Aschbacher--Smith, 15.1.29 and the conclusion of 15.1.15, p.1104.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterA.Section05To06 Section03 Section03.InitialSource
open Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]

/-- The remaining source construction must provide both inputs on one
triple of actual parabolics. No contradiction is a field of this input. -/
def CaseIComponentData.HasNaturalParabolicData {T : Sylow 2 G} {M Mc V : Subgroup G}
    (d : CaseIComponentData T M Mc V) : Prop :=
  ∃ p : CaseIComponentData.NaturalParabolics d,
    CaseIComponentData.NaturalParabolicGeometry p ∧ CaseIComponentData.NaturalRankTwoInput p

/-- Literal consumer for the full chosen local module. The parabolic
construction and earlier classification are explicit remaining inputs. -/
theorem PreparedChosenModule.source_natural_parabolic_contradiction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (d : CaseIComponentData T M Mc V) (hlinear : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnatural : d.HasNaturalMovedModule t)
    (hp : d.HasNaturalParabolicData)
    (hMS : NaturalParabolicMSClassification G) : False := by
  obtain ⟨p,a,b⟩ := hp
  exact d.false_of_natural_parabolics hG hempty hM hu h hfull hlinear
    t ht htS hnatural p a b hMS

end CFSG.Quasithin.Chapter15.Section01
