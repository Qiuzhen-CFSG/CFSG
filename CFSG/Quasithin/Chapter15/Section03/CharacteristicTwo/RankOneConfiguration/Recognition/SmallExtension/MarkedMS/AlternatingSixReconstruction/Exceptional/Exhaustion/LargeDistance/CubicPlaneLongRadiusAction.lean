module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongChains
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongCentralTransfer

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusGrowth

/-!
# Same-radius actions in the original cubic plane graph

The full-seed fixer comparison and two incident generating kernels turn
large radius images into centrality at the intermediate stabilizers.
Both radii remain in the original graph, with its actual cubic kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The original and selected edge kernels now turn large-actor fixedness
into centrality of the selected critical line at the intermediate vertex. -/
theorem plane_long_paired_line_central_of_large_actor
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : PlanePairedBackwardShift (h := h) p)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg q.edge = stabilizer Rg a)
    (A : Subgroup (FreeAmalgam Rg))
    (hA : A ≤ Q Rg (p.walk.getVert 1))
    (hlarge : 2 < (Q Rg a).relIndex A)
    (hfixed : ⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (A : Set (FreeAmalgam Rg))) :
    ⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
      (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  have hline := plane_long_paired_shift_commutator h e hz hk hb u hR p q
  have hfirst := (le_inf hline.2.2.1 hfixed).trans
    (plane_large_image_fixed_seed h e hz hk u hR p.start_color hat A hA hlarge).1.le
  exact (le_inf hfirst hline.2.1).trans ((plane_generating_edge_seed_intersection h e hz hk u hR p.start_color
      hat q.adjacent_start hgen).le.trans inf_le_right)

include h e hz hk in
/-- The two source-(5.11) action comparisons use the very same endpoint
radius. Its full image controls the first shifted line; its intersection
with the preceding core controls the next line. Both conclusions are at
the intermediate stabilizers, with both paired edge kernels accounted for. -/
theorem plane_long_paired_same_radius_actions
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : PlanePairedBackwardShift (h := h) p)
    (r : PlanePairedBackwardShift (h := h) q.path)
    (hgenq : Q Rg (p.walk.getVert 1) ⊔ Q Rg q.edge = stabilizer Rg a)
    (hgenr : Q Rg (q.path.walk.getVert 1) ⊔ Q Rg r.edge = stabilizer Rg q.start) :
    let z := p.walk.getVert (p.walk.length-2)
    let H := ⁅Z Rg q.start,Z Rg z⁆
    let K := ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆
    (2 < (Q Rg a).relIndex (V Rg z) →
      H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
    (2 < (Q Rg q.start).relIndex (V Rg z ⊓ Q Rg a) →
      K ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))) := by
  let z := p.walk.getVert (p.walk.length-2)
  let H := ⁅Z Rg q.start,Z Rg z⁆
  have hHQ : H ≤ centralizer (Q Rg z : Set (FreeAmalgam Rg)) :=
    (le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le q.start _ q.path.critical.1.le).trans
        (Z_normalized Rg _))).trans
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg z q.path.end_color))
  have hHV : H ≤ centralizer (V Rg z : Set (FreeAmalgam Rg)) :=
    hHQ.trans (centralizer_le (V_le_Q Rg (geometry := sourceGeometry h)
      q.path.end_color (by change 2 < sourceDistance h; omega)))
  have hVedge : V Rg z ≤ Q Rg (p.walk.getVert 1) := by
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) q.path.end_color
    have hl : p.walk.length=sourceDistance h := p.length_eq_b
    have hd := SimpleGraph.dist_le ((p.walk.drop 1).take (p.walk.length-3))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-3 ≤ p.walk.length-1),
      SimpleGraph.Walk.drop_getVert,show 1+(p.walk.length-3)=p.walk.length-2 by omega] at hd
    change (cosetGraph Rg).dist z (p.walk.getVert 1)+2 < sourceDistance h
    rw [SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist (p.walk.getVert 1) (p.walk.getVert (p.walk.length-2))+2 < _
    omega
  have hedge : color Rg q.edge=true := by
    have hh := adjacent_color_ne Rg q.adjacent_start
    rw [p.start_color] at hh
    cases he : color Rg q.edge <;> simp_all
  have hAedge : V Rg z ⊓ Q Rg a ≤ Q Rg (q.path.walk.getVert 1) := by
    rw [q.first]
    exact inf_le_right.trans (Q_le_adjacent_h Rg hedge q.adjacent_start)
  have hKfixed := (plane_long_paired_shift_commutator h e hz hk hb u hR q.path r).2.2.2.2.1
  constructor
  · intro hlarge
    exact plane_long_paired_line_central_of_large_actor h e hz hk hb u hR p q hgenq (V Rg z) hVedge hlarge hHV
  · intro hlarge
    exact plane_long_paired_line_central_of_large_actor h e hz hk hb u hR q.path r hgenr
      (V Rg z ⊓ Q Rg a) hAedge hlarge
      (hKfixed.trans (centralizer_le inf_le_left))

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
