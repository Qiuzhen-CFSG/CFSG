module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicGeneratingShiftCentralization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneFourSpans
import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSourceGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFourExclusion

/-!
# A large backward image on the original cubic plane

At distance four, the original large critical path has a strict forward
Baumann slice. Retain its controlled even actor and choose an edge generating
with that actor. The transported midpoint gives an actual backward critical
path with the same strict slice. If this path had small image, its first edge
would normalize the full critical kernel. The controlled actor would put
that kernel in the starting Baumann subgroup, bounding the same slice by two.
Thus the actual backward image is large.

The same path retains its original transporter, all overlap vertices, and
its critical commutator centralizing the starting stabilizer. The proof uses
neither a Sylow hypothesis nor uniformly small critical images, and retains
the full cubic projection kernel and both moving covers.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(2), pp.925--926.
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
/-- A large plane path at distance four has an actual large generating
backward shift, retaining its strict slice and central critical commutator. -/
theorem plane_four_large_backward_configuration
    (hb4 : sourceDistance h = 4)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ∃ q : GeneratingBackwardShift h p,
      4 ≤ (Q Rg (p.walk.getVert (p.walk.length - 2))).relIndex (Z Rg q.start) ∧
      2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg q.start) ∧
      let H := ⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length - 2))⁆
      H ≤ Q Rg (alpha Rg) ∧
      H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  have hb : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hc1 : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hstrict := large_remaining_four_forward_slice_strict_at h e hz hk
    hb4 u (Or.inl hR) p hlarge
  obtain ⟨A,hAU,htwo,hAn,hdisp,t,hat,hgen⟩ :=
    large_remaining_generating_actor h e hz hk u (Or.inl hR) p hlarge
  have hAZ : A ≤ Z Rg z := hAU.trans (DistanceEight.U_le_Z Rg z)
  have hZG : Z Rg z ≤ stabilizer Rg (alpha Rg) :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical
  have hAG := hAZ.trans hZG
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) ha1 hat
  let c := act Rg g (p.walk.getVert 2)
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hc1
  have hc : color Rg c = false := (action_preserves_color Rg _ _).trans
    ((p.vertex_color (by omega)).mpr (by decide))
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hstrictC : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c) := by
    dsimp only [c]
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hstrict
  have hbad : ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length - 2)) := by
    intro hh
    have hZB := controlled_backward_kernel_le_slice h e hz hb p A hAG htwo hAn
      hdisp hat hct hgen (Z Rg c) le_rfl hh
      ((show Q Rg t ≤ stabilizer Rg c from
        fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c))
    have he := relIndex_eq_one.mpr ((DistanceEight.U_le_Z Rg c).trans hZB)
    omega
  let w : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb) hc w hw hbad
  have hq1 : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1 < 2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hback : 4 ≤ (Q Rg (p.walk.getVert (p.walk.length - 2))).relIndex (Z Rg c) := by
    by_contra! hs
    have hKN := plane_small_critical_first_edge_normalizes_kernel h e hz hk u hR q hs
    rw [hq1] at hKN
    have hKB := controlled_backward_kernel_le_slice h e hz hb p A hAG htwo hAn
      hdisp hat hct hgen (Z Rg c ⊓ Q Rg (p.walk.getVert (p.walk.length - 2)))
      inf_le_left inf_le_right hKN
    let := finite_Z Rg c
    have hidx := relIndex_le_of_le_left hKB
      (index_ne_zero_of_finite (H := (Z Rg c ⊓
        Q Rg (p.walk.getVert (p.walk.length - 2))).subgroupOf (Z Rg c)))
    rw [inf_relIndex_left] at hidx
    have hbound := ((relIndex_le_of_le_right (DistanceEight.U_le_Z Rg c)
      index_ne_zero_of_finite).trans hidx).trans_eq (small_critical_indices h e hz hk q hs).1
    omega
  have hgenZ : Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) :=
    le_antisymm (sup_le (le_sup_left.trans hgen.le) hZG)
      (hgen.ge.trans (sup_le_sup_left hAZ _))
  let shift : GeneratingBackwardShift h p :=
    ⟨c,t,g,hg,hgt,rfl,hat,hct,hgenZ,q,hq1,
      fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩
  let H := ⁅Z Rg c,Z Rg (p.walk.getVert (p.walk.length - 2))⁆
  have hHedge : H ≤ Z Rg t := by
    simpa only [hq1] using plane_critical_commutator_le_first_seed h e hz hk u hR q
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hHQt : H ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro x hx y hy
    have hh := hHedge hx
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2 y hy
  have hHend : H ≤ Z Rg (p.walk.getVert (p.walk.length - 2)) :=
    le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le c _ q.critical.1.le).trans (Z_normalized Rg _))
  have hHz : H ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) := by
    apply (hHend.trans (Z_le_Q_of_dist_lt Rg _
      ((sourceGeometry h).exists_critical _ q.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg z p.end_color)))
    rw [p.dist_end,(sourceGeometry h).distance_constant _ q.end_color]
    change p.walk.length - (p.walk.length - 2) < sourceDistance h
    omega
  have hHQ : H ≤ Q Rg (alpha Rg) := by
    apply hHend.trans (Z_le_Q_of_dist_lt Rg _
      ((sourceGeometry h).exists_critical _ q.end_color) ?_)
    rw [SimpleGraph.dist_comm,p.dist_start (Nat.sub_le _ _),
      (sourceGeometry h).distance_constant _ q.end_color]
    change p.walk.length - 2 < sourceDistance h
    omega
  refine ⟨shift,hback,hstrictC,hHQ,?_⟩
  change H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))
  apply le_centralizer_iff.mp
  rw [←hgenZ]
  exact sup_le (le_centralizer_iff.mp hHQt) (le_centralizer_iff.mp hHz)

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
