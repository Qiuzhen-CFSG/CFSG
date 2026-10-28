module
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.CoreGrowthComplete
public import CFSG.Quasithin.Chapter15.Section01.ChosenCoreIntersection
public import CFSG.Quasithin.Chapter15.Section01.OrderingSource.Assembly
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Ordering
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaFullComplete

/-!
# Complete original Omega residual theorem for the chosen module

The prepared chosen module identifies the centralizing part of the
intersection core with the local two-core. Original14.1.14 makes these
cores distinct because the unique ordering-maximal local differs from the
centralizer partner. Thus intersection-core noncentrality holds also for a
proper chosen module. This discharges the last retained input of the complete
Omega residual assembly, on its literal original action and quotient maps.

Source: Aschbacher–Smith 14.1.14–17 and15.2.3, printed pp.979–980,1104–1106.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original intersection core acts nontrivially on every prepared chosen module. -/
theorem source_chosen_core_noncentral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V) :
    ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G) := by
  have hmax := source_unique_orderingMaximal_of_centralizing hG T hempty hM hJ
  have hne := unique_ordering_maximal_ne_partner_from_source hG T hM hmax hu hmany
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    apply hMc.2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  apply (hV.intersection_core_noncentral_iff T hM.1.2 hu).mpr
  exact Chapter14.SourcePreliminaries.intersection_core_ne_local_core_from_source
    hG T hempty hM.1 ⟨hMc.1,hTMc⟩ hu hmany hne

/-- Complete original15.2.3 in the Omega row, including proper chosen modules. -/
theorem source_omega_chosen_residual_complete
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized)) :
    OmegaResidualConclusions T M Mc V hV.normalized :=
  source_omega_residual_complete hG T hempty hM hJ hu hV ho
    (source_chosen_core_noncentral hG T hempty hM hJ hu hmany hV)

end CFSG.Quasithin.Chapter15.Section02
