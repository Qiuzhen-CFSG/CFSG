module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.EqualCrossedSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Selection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenUnequalSmallFixed

/-!
# Strict opposite slices and compatible forward selection for image sixteen

The selected unequal backward source path excludes a small opposite slice.
This strictness propagation precedes any fixation of the second source line
and uses only the proved opposite-small full-kernel argument.
An external strict neighbor then supplies a crossed reciprocal selection in
both mover cases. Reversal preserves the original start and midpoint while
the two interior small movers generate that midpoint's stabilizer.

Source: MS93 (5.12)(1), printed pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "edgeMover" => fun a t : Vertex d.radical =>
  SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4

/-- A strict source slice forces the opposite slice to be strict. The
unequal backward witness is constructed from the original strict path. -/
theorem strict_opposite_slice_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (p.walk.getVert 2))) :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) := by
  by_contra! hopposite
  obtain ⟨g,hg,q,hq1,hq2,hne,_,hgen,hi,_⟩ :=
    selected_source_failure_knownSimple (e := e) (hz := hz) (hn := hn) hb hcard p hstrict
  exact SixteenSmall.sixteen_unequal_small_opposite_strict_false_knownSimple
    hcard hb p (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p)
    q hq2 (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q)
    (by simpa only [hq1] using hne) (by simpa only [hq1] using hgen)
    hi g hg rfl hopposite

/-- Strict opposite-slice propagation at every component vertex, with the
original radical and its literal projection unchanged. -/
theorem strict_opposite_slice_at_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
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
  have base := strict_opposite_slice_knownSimple hcard hb (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  have hs : 2 < (B d.radical (act d.radical g⁻¹ a)
      ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((p.act g⁻¹).walk.getVert 2)) := by
    simp only [CriticalPath.act,actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act hb2 _ _ p.start_color,
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

private theorem generated_reciprocal_path_of_strict_neighbor
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a z t delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hat : Adjacent d.radical a t)
    (hdt : Adjacent d.radical delta t)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ w, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) w,
      q.walk.getVert 2 = a ∧
      edgeMover (q.walk.getVert 2) (q.walk.getVert 1) ⊔
        edgeMover (q.walk.getVert 2) (q.walk.getVert 3) =
          stabilizer d.radical (q.walk.getVert 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfirst : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical a hat hfirst
  have hdelta : Adjacent d.radical (act d.radical x delta) (p.walk.getVert 1) := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hdt
  have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb2 _ p.start_color
      ((stabilizer d.radical a).inv_mem hx))
  have hi : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x delta)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hstrict
  have hex : ∃ g ∈ stabilizer d.radical a,
      edgeMover a (p.walk.getVert 1) ⊔ edgeMover a (act d.radical g (p.walk.getVert 1)) =
        stabilizer d.radical a ∧
      ∃ r : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical g (act d.radical x delta)) (p.walk.getVert (p.walk.length-2)),
        r.walk.getVert 1 = act d.radical g (p.walk.getVert 1) ∧
        ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
    have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p
    by_cases heq : edgeMover (act d.radical x delta) (p.walk.getVert 1) =
        edgeMover a (p.walk.getVert 1)
    · obtain ⟨g,hg,_,_,_,hcross,_,_,_,r,hr1,hover⟩ := equal_backward_crossed_knownSimple
        hcard hb p hsmall (sixteen_small_omega_centrally_generated_knownSimple hcard hb)
        hdelta heq hi
      exact ⟨g,hg,hcross,r,hr1,hover⟩
    · obtain ⟨g,hg,_,_,_,hcross,_,_,r,hr1,hover⟩ := unequal_backward_crossed_knownSimple
        hcard hb p hsmall hdelta heq hi
      exact ⟨g,hg,hcross,r,hr1,hover⟩
  obtain ⟨g,_,hcross,r,hr1,hover⟩ := hex
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  let r' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g (act d.radical x delta)) (p.walk.getVert 2) := {
    start_color := r.start_color
    walk := r.walk.copy rfl he
    shortest := by rw [SimpleGraph.Walk.length_copy,r.shortest,he]
    critical := by simpa only [he] using r.critical }
  have hrl : r'.walk.length = 4 := r'.length_eq_b.trans hb
  have hr1' : r'.walk.getVert 1 = act d.radical g (p.walk.getVert 1) := by
    simpa only [r',SimpleGraph.Walk.getVert_copy] using hr1
  have hr2 : r'.walk.getVert 2 = a := by
    simpa only [r',SimpleGraph.Walk.getVert_copy,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
      using hover 0 (Nat.zero_le _)
  have hr3 : r'.walk.getVert 3 = p.walk.getVert 1 := by
    simpa only [r',SimpleGraph.Walk.getVert_copy] using hover 1 (by omega)
  let q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2)
      (act d.radical g (act d.radical x delta)) :=
    ⟨r'.end_color,r'.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,r'.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc r'⟩
  have hq (i : ℕ) : q.walk.getVert i = r'.walk.getVert (4-i) := by
    change r'.walk.reverse.getVert i = _
    rw [SimpleGraph.Walk.getVert_reverse,hrl]
  refine ⟨_,q,?_,?_⟩
  · simpa only [hq,Nat.reduceSub] using hr2
  · simpa only [hq,Nat.reduceSub,hr1',hr2,hr3] using hcross

/-- A strict image-sixteen path has a critical path with the same original
start and midpoint whose two interior small movers generate the midpoint
stabilizer. The equal and unequal external-neighbor branches both retain
actual crossed generation; no second-line fixation is assumed. -/
theorem strict_generated_forward_path_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ w, ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      q.walk.getVert 2 = p.walk.getVert 2 ∧
      edgeMover (q.walk.getVert 2) (q.walk.getVert 1) ⊔
        edgeMover (q.walk.getVert 2) (q.walk.getVert 3) =
          stabilizer d.radical (q.walk.getVert 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hopposite := strict_opposite_slice_knownSimple hcard hb p hstrict
  obtain ⟨g,_,b,_,hbm,_⟩ := selected_source_failure_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hstrict
  have hbl : b.walk.length = 4 := b.length_eq_b.trans hb
  let r : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2)
      (act d.radical g (p.walk.getVert 2)) :=
    ⟨b.end_color,b.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,b.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc b⟩
  have hrm : r.walk.getVert 2 = alpha d.radical := by
    change b.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hbl]
    exact hbm
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent d.radical z (p.walk.getVert 3) := by
    have hh := (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 3) (by omega))
    have hend : p.walk.getVert 4 = z := by simpa only [hl] using p.walk.getVert_length
    rw [show 3+1=4 from rfl,hend] at hh
    exact adjacent_symm d.radical hh
  obtain ⟨w,q,hqm,hqgen⟩ := generated_reciprocal_path_of_strict_neighbor
    hcard hb r hct hzt hopposite
  let q' : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w := {
    start_color := p.start_color
    walk := q.walk.copy hrm rfl
    shortest := by rw [SimpleGraph.Walk.length_copy,q.shortest,hrm]
    critical := by simpa only [hrm] using q.critical }
  refine ⟨w,q',?_,?_⟩
  · simpa only [q',SimpleGraph.Walk.getVert_copy] using hqm
  · simpa only [q',SimpleGraph.Walk.getVert_copy] using hqgen

omit [Finite G] in
private theorem forward_mover_act (g : FreeAmalgam d.radical) (a t : Vertex d.radical) :
    edgeMover (act d.radical g a) (act d.radical g t) =
      (edgeMover a t).map (MulAut.conj g⁻¹).toMonoidHom := by
  dsimp only
  rw [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,U_act,Q_act,Q_act]

/-- Compatible forward mover generation at an arbitrary original starting
vertex, retaining its original strict midpoint. -/
theorem strict_generated_forward_path_at_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ w, ∃ q : CriticalPath d.radical (replacementGeometry h d) a w,
      q.walk.getVert 2 = p.walk.getVert 2 ∧
      edgeMover (q.walk.getVert 2) (q.walk.getVert 1) ⊔
        edgeMover (q.walk.getVert 2) (q.walk.getVert 3) =
          stabilizer d.radical (q.walk.getVert 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := strict_generated_forward_path_knownSimple hcard hb (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  have hi : 2 < (B d.radical (act d.radical g⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((p.act g⁻¹).walk.getVert 2)) := by
    simp only [CriticalPath.act,actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act hb2 _ _ p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  obtain ⟨w,q,hqm,hqgen⟩ := base (p.act g⁻¹) hi
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  let r := q.act g
  let r' : CriticalPath d.radical (replacementGeometry h d) a (act d.radical g w) := {
    start_color := p.start_color
    walk := r.walk.copy (hcancel a) rfl
    shortest := by rw [SimpleGraph.Walk.length_copy,r.shortest,hcancel]
    critical := by simpa only [hcancel] using r.critical }
  have hr (i : ℕ) : r'.walk.getVert i = act d.radical g (q.walk.getVert i) := by
    change (r.walk.copy (hcancel a) rfl).getVert i = _
    rw [SimpleGraph.Walk.getVert_copy]
    exact actWalk_getVert d.radical g q.walk i
  refine ⟨_,r',?_,?_⟩
  · rw [hr,hqm]
    simp only [CriticalPath.act,actWalk_getVert,hcancel]
  · simp only [hr]
    rw [stabilizer_act]
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hqgen
    rw [Subgroup.map_sup] at hh
    exact (congrArg₂ (fun A B : Subgroup (FreeAmalgam d.radical) => A ⊔ B)
      (forward_mover_act (d := d) g (q.walk.getVert 2) (q.walk.getVert 1))
      (forward_mover_act (d := d) g (q.walk.getVert 2) (q.walk.getVert 3))).trans hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
