module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSmallSliceExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicEligibleGeneratingShifts
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSourceGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFourExclusion

/-!
# Small critical images above distance four on the original cubic plane

A large original critical image would bound every moving-cover slice on its
first edge by two. A small critical pair exists at the same vertex and has
a strict forward slice. Neighbor transitivity aligns that strict slice with
the first edge, contradicting its bound. The actual cubic kernel and the
original graph are retained throughout.

The internal import deliberately reuses the already checked controlled
backward-kernel lemma; its statement is independent of distance four.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7)--(5.11), pp.919--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
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
private theorem plane_long_generating_overlap_small
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)))
    (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg a' = stabilizer Rg a)
    (hq2 : q.walk.getVert 2 = a) :
    (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg c) < 4 := by
  by_contra! hlarge
  obtain ⟨r⟩ := plane_large_generating_backward_shift h e hz hk u hR q hlarge
  have hyz : act Rg r.transporter a = r.start := by
    simpa only [hq2] using r.start_eq
  have hlenP : p.walk.length = sourceDistance h := p.length_eq_b
  have hlenQ : q.walk.length = sourceDistance h := q.length_eq_b
  have hdist1 : (cosetGraph Rg).dist (q.walk.getVert (q.walk.length-2))
      (p.walk.getVert (p.walk.length-2)) = 2 := by
    rw [q.dist_end]
    omega
  have hdist2 : (cosetGraph Rg).dist (p.walk.getVert (p.walk.length-2)) a' = 2 := by
    rw [p.dist_end]
    omega
  have hdist : (cosetGraph Rg).dist (q.walk.getVert (q.walk.length-2)) a' ≤ 4 := by
    have hh := (cosetGraph_connected Rg).dist_triangle
      (u := q.walk.getVert (q.walk.length-2)) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  let H := ⁅Z Rg r.start,Z Rg (q.walk.getVert (q.walk.length-2))⁆
  have hHe : H ≤ Z Rg (q.walk.getVert (q.walk.length-2)) :=
    le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le r.start _ r.path.critical.1.le).trans
        (Z_normalized Rg _))
  have hcent (w : Vertex Rg) (hw : color Rg w = false)
      (hdist : (cosetGraph Rg).dist (q.walk.getVert (q.walk.length-2)) w < sourceDistance h) :
      H ≤ centralizer (Z Rg w : Set (FreeAmalgam Rg)) := by
    apply (hHe.trans (Z_le_Q_of_dist_lt Rg _
      ((sourceGeometry h).exists_critical _ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg w hw)))
    rwa [(sourceGeometry h).distance_constant _ r.path.end_color]
  have hnc := AlternatingSixReconstruction.Exceptional.OriginalSylow.critical_commutator_not_central_at_shift_vertex h e hz hk r.path
    c t a a' (by rw [r.first]; exact r.adjacent_start)
    hct hgen (hcent _ p.end_color (by omega)) r.transporter r.transporter_mem hyz
  have hHt : H ≤ Z Rg r.edge := by
    simpa only [r.first] using plane_critical_commutator_le_first_seed h e hz hk u hR r.path
  have ht : color Rg r.edge = true := by
    have hh := adjacent_color_ne Rg r.adjacent_start
    rw [q.start_color] at hh
    cases he : color Rg r.edge <;> simp_all
  have hHQ : H ≤ centralizer (Q Rg r.edge : Set (FreeAmalgam Rg)) := by
    intro x hx
    have hh := hHt hx
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  apply hnc
  change H ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))
  apply le_centralizer_iff.mp
  rw [←r.generation]
  exact sup_le (le_centralizer_iff.mp hHQ)
    (le_centralizer_iff.mp (hcent _ q.end_color (by omega)))

include h e hz hk in
private theorem plane_long_large_first_edge_slice_bound
    (hb : 4 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg)))
    (hdelta : Adjacent Rg delta (p.walk.getVert 1)) :
    (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta) ≤ 2 := by
  by_contra! hstrict
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨A,hAU,htwo,hAn,hdisp,t,hat,hgen⟩ :=
    large_remaining_generating_actor h e hz hk u (Or.inl hR) p hlarge
  have hAZ : A ≤ Z Rg z := hAU.trans (DistanceEight.U_le_Z Rg z)
  have hZG : Z Rg z ≤ stabilizer Rg (alpha Rg) :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical
  have hAG := hAZ.trans hZG
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) ha1 hat
  let c := act Rg g delta
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hdelta
  have hc : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h1
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hstrictC : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c) := by
    dsimp only [c]
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hstrict
  have hbad : ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    intro hh
    have hZB := controlled_backward_kernel_le_slice h e hz hb2 p A hAG htwo hAn
      hdisp hat hct hgen (Z Rg c) le_rfl hh
      ((show Q Rg t ≤ stabilizer Rg c from
        fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c))
    have he := relIndex_eq_one.mpr ((DistanceEight.U_le_Z Rg c).trans hZB)
    omega
  let w : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb2) hc w hw hbad
  have hq1 : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1 < 2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hq2 : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      p.prepend_two_overlap (Nat.le_of_lt hb2) hc w hw hbad (i := 0) (Nat.zero_le _)
  have hgenZ : Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) :=
    le_antisymm (sup_le (le_sup_left.trans hgen.le) hZG)
      (hgen.ge.trans (sup_le_sup_left hAZ _))
  have hsmall := plane_long_generating_overlap_small h e hz hk hb u hR p q hct hgenZ hq2
  have hKN := plane_small_critical_first_edge_normalizes_kernel h e hz hk u hR q hsmall
  rw [hq1] at hKN
  have hKB := controlled_backward_kernel_le_slice h e hz hb2 p A hAG htwo hAn
    hdisp hat hct hgen (Z Rg c ⊓ Q Rg (p.walk.getVert (p.walk.length-2)))
    inf_le_left inf_le_right hKN
  let := finite_Z Rg c
  have hidx := relIndex_le_of_le_left hKB
    (index_ne_zero_of_finite (H := (Z Rg c ⊓
      Q Rg (p.walk.getVert (p.walk.length-2))).subgroupOf (Z Rg c)))
  rw [inf_relIndex_left] at hidx
  have hbound := ((relIndex_le_of_le_right (DistanceEight.U_le_Z Rg c)
    index_ne_zero_of_finite).trans hidx).trans_eq (small_critical_indices h e hz hk q hsmall).1
  omega

include h e hz hk in
private theorem plane_long_large_critical_image_false_base
    (hb : 4 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) : False := by
  have hb2 : 2 < sourceDistance h := by omega
  obtain ⟨w,q,hq,_⟩ := plane_small_critical_at h e hz hk hb u hR (alpha Rg) rfl
  have hstrict := plane_small_forward_slice_strict h e hz hk hb u hR q (by rw [hq]; decide)
  have hlp : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hlq : 2 < q.walk.length := q.length_eq_b ▸ hb2
  have hatp : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hatq : Adjacent Rg (alpha Rg) (q.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hδq : Adjacent Rg (q.walk.getVert 2) (q.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hatq hatp
  have hδ : Adjacent Rg (act Rg x (q.walk.getVert 2)) (p.walk.getVert 1) := by
    rw [←hxt]
    exact (adjacent_act_iff Rg x _ _).mpr hδq
  have hbound := plane_long_large_first_edge_slice_bound h e hz hk hb u hR p hlarge hδ
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hbound
  omega

include h e hz hk in
/-- Above distance four, every original cubic plane critical pair has
image less than four. The same-edge strict-slice contradiction is literal. -/
theorem plane_long_critical_image_small
    (hb : 4 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (Q Rg z).relIndex (Z Rg a) < 4 := by
  by_contra! hlarge
  obtain ⟨g,hga⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := plane_long_large_critical_image_false_base h e hz hk hb u hR
    (z := act Rg g⁻¹ z)
  rw [←hbase] at base
  apply base (p.act g⁻¹)
  rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
  exact hlarge

include h e hz hk in
/-- Both critical seed images and the full critical commutator have order
two above distance four on the original cubic plane graph. -/
theorem plane_long_critical_indices_two
    (hb : 4 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (Q Rg z).relIndex (Z Rg a) = 2 ∧ (Q Rg a).relIndex (Z Rg z) = 2 ∧
      Nat.card (⁅Z Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) = 2 := by
  have hsmall := plane_long_critical_image_small h e hz hk hb u hR p
  have hi := small_critical_indices h e hz hk p hsmall
  exact ⟨hi.1,hi.2,small_critical_commutator_card h e hz hk p hsmall⟩

include h e hz hk in
/-- Every original cubic plane forward moving slice has index greater than
two above distance four; no critical-image premise remains. -/
theorem plane_long_forward_slice_strict
    (hb : 4 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) :=
  plane_small_forward_slice_strict_at h e hz hk hb u hR p
    (plane_long_critical_image_small h e hz hk hb u hR p)

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
