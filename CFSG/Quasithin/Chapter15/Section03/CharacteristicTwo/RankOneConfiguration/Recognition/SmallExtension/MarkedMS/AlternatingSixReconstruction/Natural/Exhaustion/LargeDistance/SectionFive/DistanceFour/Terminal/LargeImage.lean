module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.AugmentationFixed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalCover

/-!
# Exclusion of large critical images at distance four

A critical image of order at least four forces the full radius commutator
into the residual fixed core. The same conclusion holds at the midpoint:
the actual large backward path reverses to a large critical path there.
These two fixedness conclusions supply the reciprocal FF-module on the
literal moving quotient. Its central-cover bound gives derived order at
most two, contrary to the derived subgroup furnished by the large path.
Consequently every critical image at distance four has order less than
four, at every vertex of the original replacement graph.

The proof uses the completed image cases, the original six-letter marking
and both full-seed covers. It supplies the small-critical-image premise
for the remaining strict Baumann-slice exclusions.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12)(2), printed pp.925--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Large critical images fix the radius commutator at any starting vertex. -/
theorem large_radius_core_fixed_at_knownSimple
    (hb : replacementDistance h d = 4) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_radius_core_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  have hlarge₀ : 4 ≤ (Q d.radical (act d.radical g⁻¹ z)).relIndex
      (Z d.radical (act d.radical g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have hfixed := base (p.act g⁻¹) hlarge₀
  rw [V_act,Q_act,←map_commutator,fixedCore,Q_act,Ltilde_act,
    map_inf_centralizer_of_injective _ (MulAut.conj _).injective] at hfixed
  exact (map_le_map_iff_of_injective (MulAut.conj _).injective).mp hfixed

include e hz hn in
/-- The actual reciprocal FF-module excludes a large critical image. -/
theorem large_critical_image_false_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfixedA := large_radius_core_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hfixedC : ⁅V d.radical (p.walk.getVert 2),Q d.radical (p.walk.getVert 2)⁆ ≤
      fixedCore d.radical (p.walk.getVert 2) := by
    obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,hexact,t,c,hat,hct,hgen,hgenQ,
      q,hq1,hq2,hq3,hidx,hstrict,htransport,hmove,hDexact,hWN,hfix,hback⟩ :=
      full_seed_backward_large_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
    let qr : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) c :=
      ⟨q.end_color,q.walk.reverse,
        by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
        critical_reverse_pair s hc q⟩
    exact large_radius_core_fixed_at_knownSimple (e := e) (hz := hz) (hn := hn) hb qr
      (reverse_critical_image_four_le s hc (replacementDistance_pos h d) q hback)
  obtain ⟨a,z',q,hq,hfixed,hff⟩ := large_reciprocal_moved_ff_at_large_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge hfixedA hfixedC
  exact large_reciprocal_ff_false_knownSimple s hc hb q hq hfixed hff

include e hz hn in
/-- Every critical image at distance four has order less than four. -/
theorem critical_image_small_at_knownSimple
    (hb : replacementDistance h d = 4) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    (Q d.radical z).relIndex (Z d.radical a) < 4 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_critical_image_false_knownSimple
    (e := e) (hz := hz) (hn := hn) hb (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  by_contra! hlarge
  apply base (p.act g⁻¹)
  rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
  exact hlarge

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
