module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.ChoiceConstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductEstimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Transport

/-!
# Retaining the nested orbit span in the source calculation

The preceding centrality clause supplies local commutator control and hence
the selected-product lower bound for H. A regular turn identifies the two
seeds of the midpoint orbit span. Covariance under the actual right action
then puts every selected span inside the second hat layer. This retains the
conjugator information that a radius-four bound alone would lose.

Source: Meierfrankenfeld--Stellmacher (1993), concluding calculation of (4.4)
and (4.5.1)(iv)--(v), printed pp.895--896.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Layer
open PathCentrality PathCentrality.LocalCommutator
open PathCentrality.FinalCalculation.Conclusion
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The preceding centrality clause fixes the radius displacement under Ltilde. -/
theorem radius_displacement_le_fixed (earlier : Earlier R geometry)
    {c : Vertex R} (hc : color R c = false) : ⁅V R c, Q R c⁆ ≤ fixedCore R c := by
  refine le_inf ?_ ?_
  · exact (commutator_mono (PathCentrality.V_le_Q R hc (by rw [earlier.distance]; decide))
      le_rfl).trans (Subgroup.commutator_le_self _)
  · rintro x hx y hy
    obtain ⟨z, hz, rfl⟩ := earlier.centrality c hc hx
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, map_subtype_le _ hy⟩)

/-- Inside this later theorem, (4.4) centrality makes the exceptional
antecedent of local control impossible. This is not a proof of (4.4). -/
theorem localControl_of_earlier (earlier : Earlier R geometry) : LocalCommutatorControl R := by
  intro a c _ hc hd hn
  have hZV : Z R a ≤ V R c := le_iSup_of_le a (le_iSup_of_le hd.le le_rfl)
  exact (hn ((commutator_mono hZV le_rfl).trans
    (radius_displacement_le_fixed earlier hc))).elim

/-- The constructed source choices already give the unconditional lower
bound for H under the preceding (4.4) outputs. -/
theorem H_card_lower [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) : ∀ c, color R c = false → 4 ≤ Nat.card (H R c) := by
  obtain ⟨e⟩ := earlier.extended (alpha R) rfl
  have hb : 6 < geometry.b R := by rw [earlier.distance]; decide
  have hl := localControl_of_earlier earlier
  have hcard := ProductSource.terminalProduct_card_of_source_choices common hb hl
    (fun p hp => earlier.replacement _ _ p hp) earlier.natural_section e
  exact (ProductEstimates.fixed_and_H_lower common hb earlier.natural_section e hcard
    (ProductSource.terminalProduct_le_fixed hb hl e)).2

/-- A regular midpoint turn and an actual conjugator at a retain the
selected span in the literal nested orbit layer. -/
theorem conjugate_span_le_hatW {a c d : Vertex R}
    (hturn : ∃ k ∈ stabilizer R c, act R k d = a)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a) :
    localZSpan R a (act R g c) ≤ hatW R a c d := by
  obtain ⟨k, hk, ht⟩ := hturn
  have hseed : localZSpan R a c = hatV R c d := by
    rw [← ht]
    exact CriticalCase.span_eq_of_local_conjugator hk
  have hga : act R g a = a := hg
  rw [← hga, CriticalCase.localZSpan_act, hga, hseed]
  exact le_iSup (fun h : stabilizer R a =>
    NormalizerTransfer.rightConjugate (hatV R c d) h) ⟨g, hg⟩

/-- Application to the actual selected witnesses at b=8, retaining their
common conjugator and the regular turn at the marked midpoint. -/
theorem selected_span_le_hatW (earlier : Earlier R geometry) {a : Vertex R}
    {e : RegularPaths.ExtendedPath geometry a} (s : ProductSource.SelectedVertex e) :
    localZSpan R a s.delta ≤ hatW R a (e.walk.getVert 6) (e.walk.getVert 8) := by
  rw [← s.delta_eq]
  apply conjugate_span_le_hatW _ s.mem_stabilizer
  obtain ⟨k, hk, ht⟩ := e.turns 6 (by decide) (by decide) (by rw [earlier.distance]; decide)
  exact ⟨k, hk, by simpa only [e.center_eq] using ht⟩

/-- Both independent Ri lie in the second-layer displacement, with no
replacement by a radius ball. -/
theorem terminalProduct_le_hatW_displacement [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    terminalProduct e ≤ ⁅hatW R a (e.walk.getVert 6) (e.walk.getVert 8),
      Z R (e.walk.getVert 8)⁆ := by
  have hb : 6 < geometry.b R := by rw [earlier.distance]; decide
  obtain ⟨pair⟩ := ProductSource.selectedPair_nonempty common hb
    (fun p hp => earlier.replacement _ _ p hp) e
  rw [(pair.card_and_product common hb (localControl_of_earlier earlier)
    earlier.natural_section).2]
  apply sup_le
  all_goals
    change ⁅localZSpan R a _, Z R (e.walk.getVert (geometry.b R))⁆ ≤ _
    rw [earlier.distance]
    exact commutator_mono (selected_span_le_hatW earlier _) le_rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Layer
