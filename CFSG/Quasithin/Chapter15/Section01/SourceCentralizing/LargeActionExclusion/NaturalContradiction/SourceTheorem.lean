module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.CharacteristicSource

/-!
# Original 15.1.29 on the natural moved module

The original natural marking constructs the parabolics and their rank-two
input on one flag. The specialized MS argument supplies a nontrivial
characteristic subgroup of its literal Q₂, normal in KQ₂. The established
normalizer and generation argument then contradicts movement of V₂.
Every local construction and MS premise is discharged.

Source: Aschbacher--Smith, 15.1.29, printed pp.1103--1104.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Apply the proved characteristic-subgroup theorem to the original
parabolic geometry, keeping the same Sylow subgroup and radical. -/
theorem false_of_natural_parabolics_without_ms
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (d : CaseIComponentData T M Mc V) (hlinear : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnatural : d.HasNaturalMovedModule t)
    (p : NaturalParabolics d) (a : NaturalParabolicGeometry p)
    (b : NaturalRankTwoInput p) : False := by
  have s := hlinear.1.nineSource_of_natural_moved_module hM hu h t ht htS hnatural
  obtain ⟨C,hC,hne,hn⟩ := b.exists_characteristic_normal_without_ms
  exact false_of_natural_parabolics_characteristic hG hempty hM h hfull s a C hC hne hn

/-- Original 15.1.29: the original moved module cannot be natural. The
parabolic construction and the required MS consequence are both proved. -/
theorem false_of_natural_moved_module_without_ms
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) : False := by
  obtain ⟨p,a,b⟩ :=
    hasNaturalParabolicData_of_natural_moved_module hG hM hJ hu h hfull hs t ht htS hnat
  exact d.false_of_natural_parabolics_without_ms hG hempty hM hu h hfull hs
    t ht htS hnat p a b

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
