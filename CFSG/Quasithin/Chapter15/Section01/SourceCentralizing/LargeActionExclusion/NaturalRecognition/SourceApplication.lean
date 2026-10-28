module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Assembly
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.Projection

/-!
# Applying natural recognition to the original source rows

The original component recognition supplies the natural moved module for
an element of T outside S. The faithful seed projection then forces the
four-element-plane row and recovers the original Nine source data.
The separate 15.1.29 parabolic contradiction remains with the large-action
exclusion owner.

Source: Aschbacher--Smith 15.1.28--29, printed p.1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterA.Section05To06 Section03 Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Apply the completed natural recognition to the literal source-row projection. -/
theorem HasExchangedLinearSource.nine_source
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hfull : V = localModule T M)
    (h : PreparedChosenModule T M V) : d.NineSource := by
  obtain ⟨t,ht,htS⟩ := s.1.exchange_exists
  exact s.1.nineSource_of_natural_moved_module hM hu h t ht htS
    (s.natural_moved_module hG hempty hM hmany hJ hu hne hfull h t ht htS)

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
