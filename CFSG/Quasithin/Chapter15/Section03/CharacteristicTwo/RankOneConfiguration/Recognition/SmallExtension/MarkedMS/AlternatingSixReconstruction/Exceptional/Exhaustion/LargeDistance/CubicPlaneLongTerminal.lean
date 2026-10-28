module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneConjugateKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongChains
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongRadiusKernel

/-!
# The generated radius-four tower is impossible on the original cubic plane

The source paired backward selector is applied to the reverse of the actual
path. Its full critical kernel and the same component conjugate force a
normal radius section into the Baumann slice, contradicting the strict slice.
Every paired-path and action premise is supplied internally. Only the selected
path's interior generation and radius index four remain in this local endpoint.
Source: MS93 (5.11)(1), printed pp.923--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

/-- The actual paired backward path discharges all local conjugate-kernel
premises in the radius-index-two contradiction. -/
theorem plane_long_radius_two_control_false
    (hb : 4 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hi : (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (V Rg a) = 2)
    (hcontrol : ⁅V Rg a ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),Z Rg z⁆ ≤
      Z Rg a) : False := by
  obtain ⟨q⟩ := plane_long_paired_backward_shift h e hz hk hb u hR p
  have hline := plane_long_paired_shift_commutator h e hz hk hb u hR p q
  have hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg q.start) := by
    have hBmap : (B Rg a ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj q.transporter⁻¹).toMonoidHom = B Rg a ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (show 2 < sourceDistance h by omega) a p.start_color
        ((stabilizer Rg a).inv_mem q.transporter_mem))
    rw [←q.start_eq,U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact plane_long_forward_slice_strict h e hz hk hb u hR p
  exact plane_paired_radius_two_control_false h e hz hk hb u hR p q.path
    q.adjacent_start q.adjacent_shift q.first q.cubic q.cubic_mem
    q.kernel_generation q.endpoint_generation hline.2.2.2.1 hstrict hi hcontrol

/-- No actual critical path above distance four has both generating interior
edge kernels and opposite-radius index four. -/
theorem plane_long_generated_radius_ne_four
    (hb : 4 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2)) :
    (Q Rg a).relIndex (V Rg z) ≠ 4 := by
  intro hfour
  let rev : CriticalPath Rg (sourceGeometry h) z a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant a p.start_color]
        exact sourceDistance_pos h) z p.end_color p.critical }
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have he : rev.walk.getVert (rev.walk.length-2) = p.walk.getVert 2 := by
    dsimp only [rev]
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse]
    congr 1
    omega
  have ht := plane_long_radius_four_kernel_tower h e hz hk hb u hR p hgen hfour
  have hcomm := plane_long_radius_four_kernel_commutator h e hz hk hb u hR p hgen hfour
  apply plane_long_radius_two_control_false h e hz hk hb u hR rev
  · simpa only [he] using ht.1
  · rw [he,hcomm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) z p.end_color (by
        rw [(sourceGeometry h).distance_constant z p.end_color]
        exact sourceDistance_pos h) rev.critical).trans (Z_normalized Rg z))

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
