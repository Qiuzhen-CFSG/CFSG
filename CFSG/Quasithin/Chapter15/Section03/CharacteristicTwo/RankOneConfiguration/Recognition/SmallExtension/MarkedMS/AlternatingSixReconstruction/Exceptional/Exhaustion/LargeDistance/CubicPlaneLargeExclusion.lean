module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneReciprocalSpans
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneReciprocalFF
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCentralFF
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCentralDescent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminalChart

/-!
# Exclusion of a large critical image on the original cubic plane

The actual large backward path supplies reciprocal moving-radius covers,
fixedness, and derived subgroups of order greater than two. Cubic descent
constructs the six-letter actions on the literal moving central quotients.
The reciprocal index comparison makes one action an FF module; its central
cover comparison bounds that same derived subgroup by two, a contradiction.
The original graph, radical image, and the cubic kernels are retained.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(2), pp.925--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

/-- No actual distance-four critical path on the original cubic plane has
a large image. The reciprocal FF contradiction uses genuine cubic descent. -/
theorem plane_four_large_impossible
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) : False := by
  let a := alpha Rg
  let c := p.walk.getVert 2
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha : color Rg a = false := rfl
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph Rg).dist a c = 2 := p.dist_start (by omega)
  obtain ⟨hfixedA,hfixedC⟩ :=
    plane_four_large_reciprocal_radius_core_fixed h e hz hk hb u hR p hlarge
  obtain ⟨hspanA,hspanC⟩ :=
    plane_four_large_reciprocal_moving_radius_span_cover h e hz hk hb u hR p hlarge
  obtain ⟨hlowerA,hlowerC⟩ :=
    plane_four_large_reciprocal_moving_derived_gt_two h e hz hk hb u hR p hlarge
  obtain ⟨hnonA,hnonC⟩ := cubic_reciprocal_spans_nonabelian_of_moving_lower
    (h := h) hb2 ha hc hd hspanA hspanC hlowerA hlowerC
  obtain ⟨q,hback,_⟩ := plane_four_large_backward_configuration h e hz hk hb u hR p hlarge
  let qr : CriticalPath Rg (sourceGeometry h)
      (p.walk.getVert (p.walk.length-2)) q.start :=
    ⟨q.path.end_color,q.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.path.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        _ q.path.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.path.start_color]
          exact sourceDistance_pos h) _ q.path.end_color q.path.critical⟩
  let pC : CriticalPath Rg (sourceGeometry h) c q.start := by
    simpa only [hl,Nat.reduceSub] using qr
  have hlargeC : 4 ≤ (Q Rg q.start).relIndex (Z Rg c) := by
    have hh := reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) q.path hback
    simpa only [hl,Nat.reduceSub] using hh
  obtain ⟨chartA⟩ := CubicEven.chart_nonempty h a ha
  obtain ⟨chartC⟩ := CubicEven.chart_nonempty h c hc
  have hcentralA := plane_four_large_moving_extension_central_at
    h e hz hk hb u hR p hlarge chartA
  have hcentralC := plane_four_large_moving_extension_central_at
    h e hz hk hb u hR pC hlargeC chartC
  let heA := cubic_reciprocal_moving_quotient_elementary (h := h) hb2 ha hfixedA
  let heC := cubic_reciprocal_moving_quotient_elementary (h := h) hb2 hc hfixedC
  let := heA
  let := heC
  let πA := CubicTerminalChart.projection h e hz hk chartA
  let πC := CubicTerminalChart.projection h e hz hk chartC
  obtain ⟨σA,hσA⟩ := CubicTerminalChart.exists_moving_descent
    h e hz hk chartA hcentralA heA
  obtain ⟨σC,hσC⟩ := CubicTerminalChart.exists_moving_descent
    h e hz hk chartC hcentralC heC
  have hff := cubic_reciprocal_central_ff_alternative (h := h) hb2 ha hc hd
    hfixedA hfixedC hspanA hspanC hnonA hnonC
    πA (CubicTerminalChart.core_le_projection_kernel h e hz hk chartA ha)
    (CubicTerminalChart.projection_kernel_core_odd h e hz hk chartA ha)
    πC (CubicTerminalChart.core_le_projection_kernel h e hz hk chartC hc)
    (CubicTerminalChart.projection_kernel_core_odd h e hz hk chartC hc)
    σA σC hσA hσC
  have hsq := cubic_terminal_alternating_sqtk h e hz hk
  have hfixedVVA : ⁅V Rg a,V Rg a⁆ ≤ fixedCore Rg a :=
    (commutator_mono le_rfl ((sourceGeometry h).V_le_Q hb2 a ha)).trans hfixedA
  have hfixedVVC : ⁅V Rg c,V Rg c⁆ ≤ fixedCore Rg c :=
    (commutator_mono le_rfl ((sourceGeometry h).V_le_Q hb2 c hc)).trans hfixedC
  rcases hff with hffA | hffC
  · have hu := moving_derived_le_two_of_central_ff h hb2 a ha hfixedVVA
      πA (CubicTerminalChart.projection_surjective h e hz hk chartA)
      (CubicTerminalChart.projection_residual_image h e hz hk chartA) hsq σA
      (fun g v => congrArg (fun r => r g v) hσA) hffA
    have hcard : Nat.card (⁅Vcirc Rg a,Vcirc Rg a⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
      rw [←map_subtype_commutator,card_map_of_injective (Vcirc Rg a).subtype_injective]
      exact hu
    exact (Nat.not_le_of_gt hlowerA) hcard
  · have hu := moving_derived_le_two_of_central_ff h hb2 c hc hfixedVVC
      πC (CubicTerminalChart.projection_surjective h e hz hk chartC)
      (CubicTerminalChart.projection_residual_image h e hz hk chartC) hsq σC
      (fun g v => congrArg (fun r => r g v) hσC) hffC
    have hcard : Nat.card (⁅Vcirc Rg c,Vcirc Rg c⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
      rw [←map_subtype_commutator,card_map_of_injective (Vcirc Rg c).subtype_injective]
      exact hu
    exact (Nat.not_le_of_gt hlowerC) hcard

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
