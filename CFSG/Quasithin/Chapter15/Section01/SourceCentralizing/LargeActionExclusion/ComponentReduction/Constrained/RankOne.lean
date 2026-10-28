module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Source

/-!
# Assembly of the constrained rank-one contradiction from model geometry

The source-correct reductions are re-exported from RankOne.Source: the
original constructed actor excludes the A₅ permutation block, and the
full-cover orbit-Borel argument excludes every natural L₂(2ⁿ) block. The legacy conditional assembly below
keeps its original public type, including its historical two-core contract.
It is not used to assert the source exclusion. The corrected assembly uses
the separate two-residual contract and discharges all local geometry and
actor premises in PreExclusionSource.no_constrained_rankOne.

Source: Aschbacher--Smith 15.1.21, printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- Conditional assembly on the original component. The model inputs must
be proved before this gives the source rank-one exclusion. -/
theorem PreExclusionSource.no_constrained_rankOne_of_geometry_and_actor
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hgeometry : d.ConstrainedRankOneAlternative →
      d.RankOneBorelGeometry ∨ d.RankOneExceptionalGeometry)
    (hactor : ∃ Y : Subgroup G, d.RankOnePrimeActor p Y)
    (haction : d.ConstrainedRankOneAlternative → d.RankOneExceptionalGeometry →
      ∀ Y : Subgroup G, d.RankOnePrimeActor p Y → Y ≤ centralizer (d.L : Set G)) :
    ¬ d.ConstrainedRankOneAlternative := by
  intro hrank
  rcases hgeometry hrank with hB | hE
  · have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
    have hn := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
    exact s.false_of_thompson_borel (h := h) hM.1.2 he hn hB.perfect
      (s.rankOneBorelClosure_le (h := h)) hB.thompson hB.centralizers
  · obtain ⟨Y, hY⟩ := hactor
    exact s.false_of_moving_actor_centralizes (h := h) (haction hrank hE Y hY) hY.moves

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
