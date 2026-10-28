module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongRadiusAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongCentralTransfer

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusGrowth

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusTransfer

/-!
# Intermediate critical lines on the original cubic plane graph

A central intermediate line transports into the original seed. At distance
six the two edge fixers contradict critical noncentrality; at larger distance
the same transport forces the joined radius actor to have image order two.
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

private theorem central_fixed_map {F : Type*} [Group F] (H K : Subgroup F)
    (hHK : H ≤ centralizer (K : Set F)) {x : F} (hx : x ∈ K) :
    H.map (MulAut.conj x).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hHK hx))

private theorem central_line_le_neighbor {c v w : Vertex Rg}
    (hv : Adjacent Rg c v) (hw : Adjacent Rg c w)
    (H : Subgroup (FreeAmalgam Rg))
    (hH : H ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)))
    (hHv : H ≤ Z Rg v) : H ≤ Z Rg w := by
  obtain ⟨g,hg,hgw⟩ := stabilizer_transitive_neighbors Rg c hv hw
  rw [←hgw,Z_act,←central_fixed_map H (stabilizer Rg c) hH
    ((stabilizer Rg c).inv_mem hg)]
  exact map_mono hHv

include h e hz hk in
/-- If the second shifted line were central at the intervening vertex, the
literal transporter would put it in the original seed, noncentrally, and
in the first backward edge seed. -/
theorem plane_long_paired_intermediate_central_transport
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : PlanePairedBackwardShift (h := h) p)
    (r : PlanePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))) :
    let H := ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆
    H ≤ Z Rg a ∧ H ≤ Z Rg q.edge ∧
      ¬ H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  let H := ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆
  have hline := plane_long_paired_shift_commutator h e hz hk hb u hR q.path r
  have hstart : act Rg r.transporter a = r.start := by
    have hqa : q.path.walk.getVert 2=a := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
    simpa only [hqa] using r.start_eq
  have hfixed : H.map (MulAut.conj r.transporter⁻¹).toMonoidHom = H :=
    central_fixed_map H (stabilizer Rg q.start) hcentral
      ((stabilizer Rg q.start).inv_mem r.transporter_mem)
  have hHZ : H ≤ Z Rg a := by
    have hh : H ≤ Z Rg r.start :=
      le_normalizer_iff_commutator_le_left.mp
        ((critical_Z_le_stabilizer Rg (sourceGeometry h) r.start r.path.start_color
          (by rw [(sourceGeometry h).distance_constant r.start r.path.start_color]; exact sourceDistance_pos h)
          r.path.critical).trans (Z_normalized Rg r.start))
    rw [←hstart,Z_act,←hfixed] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj r.transporter⁻¹).injective).mp hh
  refine ⟨hHZ,central_line_le_neighbor r.adjacent_start q.adjacent_shift H hcentral hline.2.1,?_⟩
  intro hHa
  apply hline.2.2.2.2.2
  have hh := (map_mono (f := (MulAut.conj r.transporter⁻¹).toMonoidHom) hHa).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [hfixed] at hh
  change H ≤ centralizer ((stabilizer Rg a).map
    (MulAut.conj r.transporter⁻¹).toMonoidHom : Set (FreeAmalgam Rg)) at hh
  rwa [←stabilizer_act,hstart] at hh

include h e hz hk in
/-- At distance six the same critical line is noncentral at the required
intermediate stabilizer, not just at its own critical start. -/
theorem plane_long_paired_intermediate_noncentral_six
    (hb : sourceDistance h = 6)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : PlanePairedBackwardShift (h := h) p)
    (r : PlanePairedBackwardShift (h := h) q.path)
    (hgenq : Q Rg (p.walk.getVert 1) ⊔ Q Rg q.edge = stabilizer Rg a) :
    ¬ ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)) := by
  intro hcentral
  obtain ⟨hHZ,hHedge,hnon⟩ := plane_long_paired_intermediate_central_transport
    h e hz hk (by omega) u hR p q r hcentral
  let rev : CriticalPath Rg (sourceGeometry h)
      (q.path.walk.getVert (q.path.walk.length-2)) r.start :=
    ⟨r.path.end_color,r.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,r.path.shortest,SimpleGraph.dist_comm],
      reverse_pair h e r.path⟩
  have hlast := plane_critical_commutator_le_first_seed h e hz hk u hR rev
  change ⁅Z Rg (q.path.walk.getVert (q.path.walk.length-2)),Z Rg r.start⁆ ≤
    Z Rg (r.path.walk.reverse.getVert 1) at hlast
  rw [commutator_comm,SimpleGraph.Walk.getVert_reverse] at hlast
  have hlp : p.walk.length=6 := p.length_eq_b.trans hb
  have hlq : q.path.walk.length=6 := q.path.length_eq_b.trans hb
  have hlr : r.path.walk.length=6 := r.path.length_eq_b.trans hb
  have he : r.path.walk.getVert (r.path.walk.length-1)=p.walk.getVert 1 := by
    rw [hlr,show 6-1=3+2 from rfl,r.overlap 3 (by omega),
      show 3=1+2 from rfl,q.overlap 1 (by omega)]
  rw [he] at hlast
  exact hnon ((le_inf hlast hHedge).trans ((plane_generating_edge_seed_intersection h e hz hk u hR p.start_color
      (by
        apply (cosetGraph_adj Rg _ _).mp
        simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
          (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)) q.adjacent_start hgenq).le.trans inf_le_right))

include h e hz hk in
/-- Above distance six, intermediate centrality would force the exact
source-(5.11) two-element image of the two indicated radius actors at the
original vertex. The endpoint radius and its next-core intersection are
kept in the same graph and the same join. -/
theorem plane_long_paired_intermediate_central_radius_index
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : PlanePairedBackwardShift (h := h) p)
    (r : PlanePairedBackwardShift (h := h) q.path)
    (hgenq : Q Rg (p.walk.getVert 1) ⊔ Q Rg q.edge = stabilizer Rg a)
    (hcentral : ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))) :
    (Q Rg a).relIndex (V Rg (p.walk.getVert (p.walk.length-2)) ⊔
      (V Rg a' ⊓ Q Rg (p.walk.getVert 2))) = 2 := by
  let H := ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆
  let z₂ := p.walk.getVert (p.walk.length-2)
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  let A := V Rg z₂ ⊔ (V Rg a' ⊓ Q Rg (p.walk.getVert 2))
  have hb4 : 4 < sourceDistance h := by omega
  obtain ⟨hHZ,hHedge,hnon⟩ := plane_long_paired_intermediate_central_transport
    h e hz hk hb4 u hR p q r hcentral
  have hlp : p.walk.length=sourceDistance h := p.length_eq_b
  have hlq : q.path.walk.length=sourceDistance h := q.path.length_eq_b
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
      (i := 0) (by omega)
  have hpt : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg (p.walk.getVert 1)=true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    cases he : color Rg (p.walk.getVert 1) <;> simp_all
  have hVedge : V Rg z₂ ≤ Q Rg (p.walk.getVert 1) := by
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) q.path.end_color
    have hd := SimpleGraph.dist_le ((p.walk.drop 1).take (p.walk.length-3))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-3 ≤ p.walk.length-1),
      SimpleGraph.Walk.drop_getVert,show 1+(p.walk.length-3)=p.walk.length-2 by omega] at hd
    change (cosetGraph Rg).dist z₂ (p.walk.getVert 1)+2 < sourceDistance h
    rw [SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist (p.walk.getVert 1) (p.walk.getVert (p.walk.length-2))+2 < _
    omega
  have hA : A ≤ Q Rg (p.walk.getVert 1) :=
    sup_le hVedge (inf_le_right.trans (Q_le_adjacent_h Rg ht hpt))
  have hHe : H ≤ Z Rg z₄ :=
    le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le r.start _ r.path.critical.1.le).trans
        (Z_normalized Rg _))
  have hd₂ : (cosetGraph Rg).dist z₂ z₄ = 2 := by
    rw [SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist (q.path.walk.getVert (q.path.walk.length-2)) _ = 2
    rw [q.path.dist_end]
    omega
  have hd₀ : (cosetGraph Rg).dist a' z₂ = 2 := by
    rw [SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist (p.walk.getVert (p.walk.length-2)) _ = 2
    rw [p.dist_end]
    omega
  have hd₄ : (cosetGraph Rg).dist a' z₄ ≤ 4 := by
    have hh := (cosetGraph_connected Rg).dist_triangle (u := a') (v := z₂) (w := z₄)
    omega
  have hV₂ : V Rg z₂ ≤ Q Rg z₄ := by
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) q.path.end_color
    change (cosetGraph Rg).dist z₂ z₄+2 < sourceDistance h
    omega
  have hV₀ : V Rg a' ≤ Q Rg z₄ := by
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) p.end_color
    change (cosetGraph Rg).dist a' z₄+2 < sourceDistance h
    omega
  have hHA : H ≤ centralizer (A : Set (FreeAmalgam Rg)) :=
    (hHe.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg z₄ r.path.end_color))).trans
        (centralizer_le (sup_le hV₂ (inf_le_left.trans hV₀)))
  have hupper : (Q Rg a).relIndex A ≤ 2 := by
    by_contra! hlarge
    exact hnon ((le_inf ((le_inf hHZ hHA).trans
      (plane_large_image_fixed_seed h e hz hk u hR p.start_color hat A hA hlarge).1.le) hHedge).trans
        ((plane_generating_edge_seed_intersection h e hz hk u hR p.start_color
      (by
        apply (cosetGraph_adj Rg _ _).mp
        simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
          (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)) q.adjacent_start hgenq).le.trans inf_le_right))
  let rev : CriticalPath Rg (sourceGeometry h) z₂ q.start :=
    ⟨q.path.end_color,q.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.path.shortest,SimpleGraph.dist_comm],
      reverse_pair h e q.path⟩
  have hescape := plane_radius_escape h e hz hk u hR rev
  have hqa : q.path.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  change ¬ V Rg z₂ ≤ Q Rg
    (q.path.walk.reverse.getVert (q.path.walk.reverse.length-2)) at hescape
  rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
    show q.path.walk.length-(q.path.walk.length-2)=2 by omega,hqa] at hescape
  have hne : (Q Rg a).relIndex A ≠ 1 := fun hh =>
    hescape (le_sup_left.trans (relIndex_eq_one.mp hh))
  let := finite_stabilizer Rg (p.walk.getVert 1)
  let : Finite A := Finite.of_injective
    (inclusion (hA.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hpos : 0 < (Q Rg a).relIndex A := Nat.pos_of_ne_zero index_ne_zero_of_finite
  change (Q Rg a).relIndex A=2
  omega

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
