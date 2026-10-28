module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.FullRadius
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.CriticalOrder
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer.Source

/-!
# Excluding the derived-only action at large critical distance

At the midpoint of an actual critical path, the full radius has derived
order at most two. An opposite critical involution acts nontrivially on
the original moved natural cover. Its commutator has order at least four
and lies in that same radius derived subgroup, giving a contradiction.
The original central cover and characteristic radical are retained.

Source: MS93 (3.8), printed pp.878--879.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (m : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
  (r : Replacement L R)

/-- The A₆ radius contradiction on the original characteristic replacement. -/
theorem alternating_impossible
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) : False := by
  let π := projection h m hz hn r
  let W := replacementMoved r
  let f := embedM r.radical
  let a := alpha r.radical
  let geometry := replacementGeometry h r
  have hb : 2 < replacementDistance h r := by rw [fg.distance]; decide
  obtain ⟨b,hcrit⟩ := criticalPair_exists r.radical a (geometry.exists_critical a rfl)
  let p := CriticalPath.ofPair (geometry := geometry) rfl hcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans fg.distance
  have hle : 2 ≤ p.walk.length := by omega
  let c := p.walk.getVert 2
  have hc : color r.radical c = false := (p.vertex_color hle).mpr (by decide)
  have hac : (cosetGraph r.radical).dist a c = 2 := p.dist_start hle
  have hcb : (cosetGraph r.radical).dist c b = 2 := by rw [p.dist_end,hl]
  have hbColor := critical_endpoint_color r.radical a rfl _ hcrit
  have hreverse := critical_reverse r.radical geometry
    (edgeCentralizerCondition h m hz hn r himage) a rfl
    (show 0 < criticalDistance r.radical a (geometry.exists_critical a rfl) by
      rw [geometry.distance_constant a rfl]; exact replacementDistance_pos h r)
    b hbColor hcrit
  obtain ⟨x,hx,hxQ⟩ := SetLike.not_le_iff_exists.mp hreverse.2
  obtain ⟨t,hat,ht⟩ := exists_adjacent_dist_sub_one r.radical a b (by
    rw [hcrit.1,geometry.distance_constant a rfl]
    exact replacementDistance_pos h r)
  have hZS : Z r.radical b ≤ stabilizer r.radical a :=
    (geometry.omega_bound b hbColor (by
      rw [geometry.distance_constant b hbColor]; exact replacementDistance_pos h r)).trans
      (((Estimates.critical_edge_data h m hz hn r himage a rfl b hcrit t hat ht).1).trans
        (CriticalCriterion.edge_le_stabilizer r.radical rfl hat))
  obtain ⟨g,hg⟩ := show x ∈ f.range from (by
    change x ∈ (embedM r.radical).range
    have hxS := hZS hx
    change x ∈ stabilizer r.radical (mVertex r.radical 1) at hxS
    rwa [stabilizer_m_base] at hxS)
  have hgne : π g ≠ 1 := by
    intro he
    have hgQ : g ∈ pCore 2 r.overgroup := by
      rw [←projection_kernel h m hz hn r]
      exact he
    apply hxQ
    change x ∈ Q r.radical (alpha r.radical)
    rw [←hg,Q_alpha r.radical (replacement_radical_isPGroup h r)
      (replacement_core_le_radical h r)]
    exact mem_map_of_mem f hgQ
  have hgsq : (π g)^2 = 1 := by
    rw [←map_pow]
    have hg2 : g^2=1 := by
      apply embedM_injective r.radical
      rw [map_pow,hg,map_one]
      let := geometry.Z_elementary (replacementDistance_pos h r) b hbColor
      exact elemPow_eq_one_of_isElementaryAbelian x hx
    rw [hg2,map_one]
  have horder : orderOf (π g) = 2 := orderOf_eq_prime hgsq hgne
  have heven : π g ∈ alternatingGroup (Fin 6) := by rw [←himage]; exact ⟨g,rfl⟩
  let := replacementMoved_normal h r
  have hfour := four_le_commutator_card_of_natural W (coverProjection h m hz hn r)
    (coverProjection_surjective h m hz hn r) π
    (fun k v => cover_conjugate h m hz hn r k v (MulAut.conjNormal k v) rfl)
    g heven horder
  have hUa : W.map f = U r.radical a :=
    (DistanceTwo.CentralLayer.replacement_centralLayer r m hz h).U_eq_moved.symm
  have hZa : Z r.radical a ≤ V r.radical c := le_iSup_of_le a (le_iSup_of_le hac.le le_rfl)
  have hZb : Z r.radical b ≤ V r.radical c := le_iSup_of_le b (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm,hcb]) le_rfl)
  have hcomm : (⁅W,zpowers g⁆).map f ≤ ⁅V r.radical c,V r.radical c⁆ := by
    rw [map_commutator,hUa,MonoidHom.map_zpowers,hg]
    exact commutator_mono ((U_le_Z a).trans hZa) (zpowers_le.mpr (hZb hx))
  let := finite_moving geometry hb c hc
  let : Finite (⁅V r.radical c,V r.radical c⁆ : Subgroup (FreeAmalgam r.radical)) := by
    rw [radius_derived_eq_moving_derived h m hz hn r himage fg c hc]
    exact Finite.of_injective (inclusion (commutator_le_self (Vcirc r.radical c)))
      (inclusion_injective _)
  have htwo := (card_le_of_le hcomm).trans (radius_derived_card_le_two h m hz hn r himage fg c hc)
  rw [card_map_of_injective (embedM_injective r.radical)] at htwo
  omega

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
