module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardAttachment
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelOppositeSlice
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.InitialSelection

/-!
# Opposite slices in the full point-core branch at distance four

The literal backward selector makes its kernel commutator central at the
starting vertex. A small opposite slice would then normalize the full
backward kernel joined with that vertex's seed. The elementary radical
action puts this join in the Baumann subgroup, contradicting the strict
slice retained by the selector. Both covers and their central attachments
are retained.

Source: MS93 (5.12)(1),(3), printed pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- A strict forward slice forces the opposite slice to be strict as well.
The backward path and its full-kernel normalization are constructed internally. -/
theorem full_point_strict_opposite_slice_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) := by
  by_contra! hopposite
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,hgen,g,hg,hgt,q,hq1,hover,hlargeq⟩ :=
    full_point_backward_shift_knownSimple hb2 u hfull p hdelta hstrict
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  let q' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g (p.walk.getVert 2)) (p.walk.getVert 2) := {
    start_color := q.start_color
    walk := q.walk.copy rfl he
    shortest := by rw [SimpleGraph.Walk.length_copy,q.shortest,he]
    critical := by simpa only [he] using q.critical }
  have hq1' : q'.walk.getVert 1 = t := by
    change (q.walk.copy rfl he).getVert 1 = t
    rwa [SimpleGraph.Walk.getVert_copy]
  have hq2' : q'.walk.getVert 2 = alpha d.radical := by
    change (q.walk.copy rfl he).getVert 2 = _
    rw [SimpleGraph.Walk.getVert_copy]
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [(full_point_four_critical_indices_two_knownSimple hb u hfull p).1]
    decide
  have hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex
      (Z d.radical (act d.radical g (p.walk.getVert 2))) < 4 := by
    rw [(full_point_four_critical_indices_two_at_knownSimple hb u hfull q').1]
    decide
  have hline := (backward_kernel_attachment s hc hb u hf p q' hat hq1' hq2'
    hgen hlargeq).2.2.1
  have hnorm := small_backward_kernel_normalized_of_opposite_slice_line_fixed
    s hc hb p hsmall q' hq2' hqsmall g hg rfl hopposite hline
  have hel : IsElementaryAbelian 2 (d.radical.map s.projection) := by
    let := pointCore_elementary
    rw [hf]
    exact IsElementaryAbelian.map _
  have hres : Ltilde d.radical (q'.walk.getVert 2) ≤
      Q d.radical (q'.walk.getVert 1) ⊔ Z d.radical z := by
    rw [hq1',hq2',hgen]
    exact Ltilde_le_stabilizer _
  have hi := elementary_small_normalized_slice_le_two s hc hb hel q' hqsmall
    (Z d.radical z) hres (by simpa only [hq2'] using hnorm)
  rw [hq2'] at hi
  exact (not_le_of_gt hlargeq) hi

include e hz hn in
/-- The same strict-slice propagation on every component vertex of the
original graph, with the original radical and projection unchanged. -/
theorem full_point_strict_opposite_slice_at_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := full_point_strict_opposite_slice_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  have hs : 2 < (B d.radical (act d.radical g⁻¹ a)
      ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((p.act g⁻¹).walk.getVert 2)) := by
    change 2 < (B d.radical _ _).relIndex
      (U d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2))
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act hb2 _ _ p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  have hi := base (p.act g⁻¹) hs
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hi' : 2 < (B d.radical (act d.radical g⁻¹ (p.walk.getVert 2))
      ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g⁻¹ z)) := by
    simpa only [CriticalPath.act,actWalk_getVert] using hi
  rwa [Escape.PairingControl.FirstPairing.B_act hb2 _ _ hcol,
    U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hi'


include e hz hn in
/-- A small opposite slice is impossible in the full point-core branch.
If the forward slice is also small, the reciprocal selected path has a
strict forward slice and a conjugate of that same small slice opposite it. -/
theorem full_point_opposite_slice_strict_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z) :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) := by
  by_contra! hopposite
  have hb2 : 2 < replacementDistance h d := by omega
  have hforward : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2 := by
    by_contra! hstrict
    exact (not_le_of_gt (full_point_strict_opposite_slice_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u hfull p hstrict)) hopposite
  have hnon := small_predecessor_selected_span_nonabelian_knownSimple hb u hfull p hopposite
  have hreverse := consecutive_small_slices_reverse_large_knownSimple hb u hfull p hforward hopposite
  obtain ⟨_,x,hx,q,_,hqm,_⟩ := selected_span_conjugate_critical_path (h := h) hb2 p hnon
  have hqs : 2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (q.walk.getVert 2)) := by
    simpa only [hqm] using hreverse
  have hi := full_point_strict_opposite_slice_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull q hqs
  rw [hqm] at hi
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom =
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 _ rfl ((stabilizer d.radical _).inv_mem hx))
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hi
  exact (not_le_of_gt hi) hforward

include e hz hn in
/-- The opposite slice is strict on every critical path of the original graph. -/
theorem full_point_opposite_slice_strict_at_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := full_point_opposite_slice_strict_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  have hi := base (p.act g⁻¹)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hi' : 2 < (B d.radical (act d.radical g⁻¹ (p.walk.getVert 2))
      ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g⁻¹ z)) := by
    simpa only [CriticalPath.act,actWalk_getVert] using hi
  rwa [Escape.PairingControl.FirstPairing.B_act hb2 _ _ hcol,
    U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hi'

include e hz hn in
/-- Every forward and opposite midpoint slice is strict in the full
point-core distance-four branch. The full-point forward extension transfers
the opposite-slice result back to the original forward slice. -/
theorem full_point_all_slices_strict_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∧
      2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical z) := by
  refine ⟨?_,full_point_opposite_slice_strict_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull p⟩
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let r : CriticalPath d.radical (replacementGeometry h d) z a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hrm : r.walk.getVert 2 = p.walk.getVert 2 := by
    change p.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hl]
  obtain ⟨w,q,_,_,hqend⟩ := (full_point_forward_path_knownSimple hb2 u hfull r).2.2
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hqm : q.walk.getVert 2 = a := by simpa only [hql,Nat.reduceSub] using hqend
  let qr : CriticalPath d.radical (replacementGeometry h d) w (r.walk.getVert 2) :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc q⟩
  have hqrm : qr.walk.getVert 2 = a := by
    change q.walk.reverse.getVert 2 = a
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hqm
  have hi := full_point_opposite_slice_strict_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull qr
  simpa only [hqrm,hrm] using hi


include e hz hn in
/-- The literal strict backward selector forces central generation of the
whole omega layer at every component vertex in the full point-core branch. -/
theorem full_point_omega_centrally_generated_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) :
    ∀ v : Vertex d.radical, color d.radical v = false →
      X d.radical v = U d.radical v ⊔
        (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))) := by
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  have hstrict := (full_point_all_slices_strict_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull p).1
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,hgen,g,hg,hgt,q,hq1,hover,hlargeq⟩ :=
    full_point_backward_shift_knownSimple hb2 u hfull p hdelta hstrict
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  let q' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g (p.walk.getVert 2)) (p.walk.getVert 2) := {
    start_color := q.start_color
    walk := q.walk.copy rfl he
    shortest := by rw [SimpleGraph.Walk.length_copy,q.shortest,he]
    critical := by simpa only [he] using q.critical }
  have hq1' : q'.walk.getVert 1 = t := by
    change (q.walk.copy rfl he).getVert 1 = t
    rwa [SimpleGraph.Walk.getVert_copy]
  have hq2' : q'.walk.getVert 2 = alpha d.radical := by
    change (q.walk.copy rfl he).getVert 2 = _
    rw [SimpleGraph.Walk.getVert_copy]
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [(full_point_four_critical_indices_two_knownSimple hb u hfull p).1]
    decide
  have hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex
      (Z d.radical (act d.radical g (p.walk.getVert 2))) < 4 := by
    rw [(full_point_four_critical_indices_two_at_knownSimple hb u hfull q').1]
    decide
  have hnear : (cosetGraph d.radical).dist
      (act d.radical g (p.walk.getVert 2)) (alpha d.radical) ≤ 2 := by
    have hh := q'.dist_start (i := 2) (by have hql := q'.length_eq_b.trans hb; omega)
    simpa only [hq2'] using hh.le
  apply (small_backward_kernel_normalized_or_centrally_generated s hc hb p hsmall
    q'.start_color hnear).resolve_left
  intro hnorm
  have hel : IsElementaryAbelian 2 (d.radical.map s.projection) := by
    let := pointCore_elementary
    rw [hf]
    exact IsElementaryAbelian.map _
  have hres : Ltilde d.radical (q'.walk.getVert 2) ≤
      Q d.radical (q'.walk.getVert 1) ⊔ Z d.radical z := by
    rw [hq1',hq2',hgen]
    exact Ltilde_le_stabilizer _
  have hi := elementary_small_normalized_slice_le_two s hc hb hel q' hqsmall
    (Z d.radical z) hres (by simpa only [hq2'] using hnorm)
  rw [hq2'] at hi
  exact (not_le_of_gt hlargeq) hi

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

