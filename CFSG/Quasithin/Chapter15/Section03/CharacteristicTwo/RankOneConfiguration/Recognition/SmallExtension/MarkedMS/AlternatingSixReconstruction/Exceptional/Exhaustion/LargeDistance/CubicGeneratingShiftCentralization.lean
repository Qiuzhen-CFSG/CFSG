module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicEligibleGeneratingShifts

/-!
# Centralization of a generating backward shift

A large critical image on the literal cubic plane produces a generating
backward shift.  Its shifted critical commutator lies in the first edge seed
of the shifted path.  The seed centralizes the edge two-core, while the
commutator lies in the original endpoint two-core by the distance estimate.
The generation identity for the shift therefore puts this commutator in the
starting `Q`-group and in the centralizer of the whole starting stabilizer.
No Sylow replacement, global small-image premise, or reconstruction input is
used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
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

include h e hz hk in
/-- A large plane image yields a shifted critical commutator in the
starting `Q`-group, centralizing the starting stabilizer. -/
theorem plane_large_shift_commutator_centralized
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a)) :
    ∃ q : GeneratingBackwardShift h p,
      let c := p.walk.getVert (p.walk.length - 2)
      let H := ⁅Z Rg q.start, Z Rg c⁆
      H ≤ Q Rg a ∧ H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  obtain ⟨q⟩ := plane_large_generating_backward_shift h e hz hk u hR p hlarge
  have hb := distance_gt_two h e hz hk
  have hlen : p.walk.length = sourceDistance h := p.length_eq_b
  let c := p.walk.getVert (p.walk.length - 2)
  let H := ⁅Z Rg q.start, Z Rg c⁆
  have hHc : H ≤ Z Rg c :=
    le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le q.start _ q.path.critical.1.le).trans
        (Z_normalized Rg _))
  have hHedge : H ≤ Z Rg q.edge := by
    dsimp only [H]
    simpa only [q.first] using
      plane_critical_commutator_le_first_seed h e hz hk u hR q.path
  have hqedge : color Rg q.edge = true := by
    have hh := adjacent_color_ne Rg q.adjacent_start
    rw [p.start_color] at hh
    cases heq : color Rg q.edge <;> simp_all
  have hHq : H ≤ centralizer (Q Rg q.edge : Set (FreeAmalgam Rg)) := by
    intro x hx y hy
    have hh := hHedge hx
    rw [Z,if_neg (by simp [hqedge])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2 y hy
  have hHz : H ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) := by
    apply (hHc.trans (Z_le_Q_of_dist_lt Rg c
      ((sourceGeometry h).exists_critical _ q.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg z p.end_color)))
    change (cosetGraph Rg).dist (p.walk.getVert (p.walk.length - 2)) z < _
    rw [p.dist_end,(sourceGeometry h).distance_constant _ q.path.end_color]
    change p.walk.length - (p.walk.length - 2) < sourceDistance h
    omega
  have hHQa : H ≤ Q Rg a := by
    apply hHc.trans (Z_le_Q_of_dist_lt Rg c
      ((sourceGeometry h).exists_critical _ q.path.end_color) ?_)
    change (cosetGraph Rg).dist (p.walk.getVert (p.walk.length - 2)) a < _
    rw [SimpleGraph.dist_comm,p.dist_start (Nat.sub_le _ _),
      (sourceGeometry h).distance_constant _ q.path.end_color]
    change p.walk.length - 2 < sourceDistance h
    omega
  have hHstab : H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←q.generation]
    exact sup_le (le_centralizer_iff.mp hHq) (le_centralizer_iff.mp hHz)
  exact ⟨q, hHQa, hHstab⟩

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
