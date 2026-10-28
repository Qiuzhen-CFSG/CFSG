module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Source
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Inputs

/-!
# The representative seed from original selection

The original plane-stabilizer source theorem and the ordering controls
produce the literal Sylow subgroup of each fixed-line centralizer. The
actual central four-plane therefore supplies its representative involution
with the selected fixed line and ambient Sylow. Source: Aschbacher–Smith
15.3.6 and15.3.38, printed pp.1122 and1136.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Both definite planes have the literal selected stabilizer S. -/
theorem CharacteristicTwo.LocalData.planeStabilizer_eq_S
    (d : CharacteristicTwo.LocalData G) (i : OrthogonalPlaneIndex) :
    planeStabilizer d.T (d.action.plane i) = d.S := by
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hn : (⟨x, d.sylow_le hx.1⟩ : d.M) ∈
        (normalizer (d.action.plane i : Set G)).subgroupOf d.M := hx.2
    rw [d.action.plane_normalizer_eq_comap,
      OrthogonalGeometry.setwise_plane_eq_ker] at hn
    change (⟨x, d.sylow_le hx.1⟩ : d.M) ∈
      (normalizer (d.action.plane 1 : Set G)).subgroupOf d.M
    rwa [d.action.plane_normalizer_eq_comap, OrthogonalGeometry.setwise_plane_eq_ker]
  · exact le_inf inf_le_left (OutsideStructure.LocalBranches.s_normalizes_plane d i)

/-- The selected stabilizer fixes the original four-group. -/
theorem CharacteristicTwo.LocalData.card_ZS (d : CharacteristicTwo.LocalData G) :
    Nat.card d.ZS = 4 := d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1

/-- Original15.3.6 supplies the actual Sylow subgroup in either fixed-line
centralizer, with the original selection hypotheses discharged. -/
theorem source_fixed_line_sylow_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (i : OrthogonalPlaneIndex) :
    Chapter1.IsSylowIn 2 d.S (centralizer (fixedPlane (d.action.plane i) d.S : Set G)) := by
  obtain ⟨_, hBaum, _⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have hs := (source_lemma_15_3_6 d.T d.action hM hBaum i).2.2.1
  change Chapter1.IsSylowIn 2 (planeStabilizer d.T (d.action.plane i))
    (centralizer (fixedPlane (d.action.plane i) (planeStabilizer d.T (d.action.plane i)) : Set G)) at hs
  rw [d.planeStabilizer_eq_S i] at hs
  exact hs

namespace DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel GlobalGeometry

/-- The actual representative seed retains its fixed line and ambient Sylow.
The marked-envelope argument uses this literal v, not a model involution. -/
theorem LocalResult.exists_representative_seed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I L : Subgroup G} (r : LocalResult d I L) :
    ∃ v : G, v ≠ 1 ∧ orderOf v = 2 ∧
      zpowers v = d.ZS ⊓ r.cover.borel.W₁ ∧
      d.S ≤ centralizer ({v} : Set G) ∧
      Chapter1.IsSylowIn 2 d.S (centralizer ({v} : Set G)) := by
  obtain ⟨i, hi⟩ := r.plane
  obtain ⟨v, hv1, hv2, hline, hSv⟩ := exists_fixed_line_generator r.cover.borel.W₁ d.ZS d.S
    inf_le_right (by rw [hi]; exact source_fixed_line_card d d.card_ZS i)
  refine ⟨v, hv1, hv2, hline, hSv, ?_⟩
  exact representative_sylow_of_fixed_line d.V r.cover.borel.W₁ d.ZS d.S
    (hi ▸ d.action.plane_le i) rfl v hline
    (hi ▸ source_fixed_line_sylow_from_selection hG d hempty hM hu hmany i)

end DiagonalOuter.CoverReduction.Assembly

end CFSG.Quasithin.Chapter15.Section03
