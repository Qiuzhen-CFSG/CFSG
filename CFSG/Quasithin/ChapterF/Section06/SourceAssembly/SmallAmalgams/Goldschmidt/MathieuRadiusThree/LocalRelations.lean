module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsParity
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsFlip
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsIntersectionTrack
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsOrder
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsTransport

/-!
# The original radius-three local relations

Even local permutations centralize the folded three-label product. If an
odd local permutation exists, the literal single flips put both center
labels into the nearby commutator. Its four-group intersection and the
nondegenerate track commutator then force the same two-label identity.
That identity gives the radius-two eight-group and all six-arc relations;
the eight-group excludes odd permutations and identifies the local image
with the symmetric group on four points.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12.2)--(6.12.5), printed pp.403--404.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
universe u
variable {G : Type u} [Group G] {F : Bool → Subgroup G} {s : ℕ}
/-- Goldschmidt (6.12.3) on the actual chosen translation track. -/
theorem CanonicalLabelSetup.radiusThree_track_commutator
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3) :
    ⁅d.label (d.track.vertex (d.center-2)), d.label (d.track.vertex (d.center+4))⁆ =
      d.label (d.track.vertex d.center) * d.label (d.track.vertex (d.center+2)) := by
  classical
  obtain ⟨f,hfc⟩ := d.exists_radiusThree_foldedBranchFrame h.action.toCubicTreeAction hr
  by_cases he : (f.blockAction h.action.toCubicTreeAction).range ≤ evenModel
  · exact d.radiusThree_track_commutator_of_even h hr f hfc he
  · let a := d.track.vertex d.center
    let b := d.track.vertex (d.center+2)
    have ha : a.type = d.side := d.center_type
    have hb : b.type = d.side := by simpa only [b,mul_one] using d.shifted_type 1
    have hab : (RankTwo.graph F).dist a b = 2 := by
      apply (DistanceTwoGeometry.dist_eq_two_iff h.action.tree).mpr
      refine ⟨?_,d.track.vertex (d.center+1),d.track.adjacent d.center,?_⟩
      · intro hh
        have hh' := d.track.injective hh
        omega
      · simpa only [show d.center+1+1=d.center+2 by omega] using d.track.adjacent (d.center+1)
    obtain ⟨fb⟩ := h.action.toCubicTreeAction.exists_branchFrame b
    have heb : ¬ (fb.blockAction h.action.toCubicTreeAction).range ≤ evenModel := by
      intro hh
      exact he ((f.blockAction_even_iff_of_same_type h fb (ha.trans hb.symm)).mpr hh)
    have hza := d.label_mem_nearby_commutator_of_not_even h hr ha hab f he
    have hzb := d.label_mem_nearby_commutator_of_not_even h hr hb
      (by simpa only [dist_comm] using hab) fb heb
    apply d.radiusThree_track_commutator_of_labels_mem_commutator h hr hza
    simpa only [Subgroup.commutator_comm] using hzb

namespace MathieuRadiusThree
/-- The literal local relations (6.12.2)--(6.12.5) follow from the original
large-action and radius-three source hypotheses. -/
theorem localRelations {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (hr : d.radius = 3) : LocalRelations h d := by
  have ht := d.radiusThree_track_commutator h hr
  have hc := d.radiusTwo_card_eq_eight_of_track_commutator h hr ht
  refine ⟨?_,hc,?_⟩
  · intro a ha f
    exact f.blockAction_symmetricFour_of_labelBall_card_eight h d hr ha (hc a ha)
  · exact d.six_arc_of_radiusThree_track_commutator h hr ht

/-- The complete source producer of the radius-three local relation input. -/
theorem localRelationsInput : LocalRelationsInput.{u} := by
  intro G _ F s h d hr
  exact localRelations hr
end MathieuRadiusThree
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
