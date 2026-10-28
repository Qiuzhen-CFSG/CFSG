module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.OppositeSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEscape

/-!
# Generated forward selection from a strict mixed slice

An external strict neighbor supplies backward escape after the paired edge
selection. Applying this to a reciprocal critical path retains the original
start and midpoint, and gives generation by the two interior edge kernels.
The narrow private import reuses the relative backward shift without
widening the older escape module's public API.

Source: MS93 (5.12)(3), printed pp.926--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem generated_reciprocal_path_of_strict_neighbor
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z t delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hdt : Adjacent d.radical delta t)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ w, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) w,
      q.walk.getVert 2 = alpha d.radical ∧
      Q d.radical (q.walk.getVert 1) ⊔ Q d.radical (q.walk.getVert 3) =
        stabilizer d.radical (q.walk.getVert 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t',hat',hpair,hgen⟩ := mixed_small_aligned_generating_neighbor_knownSimple hb u him p
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hat hat'
  have hct : Adjacent d.radical (act d.radical x delta) t' := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hdt
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb2 _ rfl
      ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hi : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x delta)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hstrict
  obtain ⟨k,_,r,hr1,hover,_⟩ := MixedEscape.relative_small_backward_shift s hc hb2 u hf p
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p)
    hat' hct hgen hi
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  let r' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical k (act d.radical x delta)) (p.walk.getVert 2) := {
    start_color := r.start_color
    walk := r.walk.copy rfl he
    shortest := by rw [SimpleGraph.Walk.length_copy,r.shortest,he]
    critical := by simpa only [he] using r.critical }
  have hrl : r'.walk.length = 4 := r'.length_eq_b.trans hb
  have hr1' : r'.walk.getVert 1 = t' := by
    simpa only [r',SimpleGraph.Walk.getVert_copy] using hr1
  have hr2 : r'.walk.getVert 2 = alpha d.radical := by
    simpa only [r',SimpleGraph.Walk.getVert_copy,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
      using hover 0 (Nat.zero_le _)
  have hr3 : r'.walk.getVert 3 = p.walk.getVert 1 := by
    simpa only [r',SimpleGraph.Walk.getVert_copy] using hover 1 (by omega)
  let q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2)
      (act d.radical k (act d.radical x delta)) :=
    ⟨r'.end_color,r'.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,r'.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc r'⟩
  have hq (i : ℕ) : q.walk.getVert i = r'.walk.getVert (4-i) := by
    change r'.walk.reverse.getVert i = _
    rw [SimpleGraph.Walk.getVert_reverse,hrl]
  refine ⟨_,q,?_,?_⟩
  · simpa only [hq,Nat.reduceSub] using hr2
  · simpa only [hq,Nat.reduceSub,hr1',hr2,hr3] using hpair

private theorem generated_reciprocal_path_of_strict_neighbor_at
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z t delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hat : Adjacent d.radical a t)
    (hdt : Adjacent d.radical delta t)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ w, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) w,
      q.walk.getVert 2 = a ∧
      Q d.radical (q.walk.getVert 1) ⊔ Q d.radical (q.walk.getVert 3) =
        stabilizer d.radical (q.walk.getVert 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := generated_reciprocal_path_of_strict_neighbor hb u him
    (z := act d.radical g⁻¹ z) (t := act d.radical g⁻¹ t) (delta := act d.radical g⁻¹ delta)
  rw [←hbase] at base
  have hi : 2 < (B d.radical (act d.radical g⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g⁻¹ delta)) := by
    rw [Escape.PairingControl.FirstPairing.B_act hb2 _ _ p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  obtain ⟨w,q,hqm,hqgen⟩ := base (p.act g⁻¹)
    ((adjacent_act_iff d.radical g⁻¹ _ _).mpr hat)
    ((adjacent_act_iff d.radical g⁻¹ _ _).mpr hdt) hi
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hs : act d.radical g ((p.act g⁻¹).walk.getVert 2) = p.walk.getVert 2 := by
    simp only [CriticalPath.act,actWalk_getVert,hcancel]
  let r := q.act g
  let r' : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2)
      (act d.radical g w) := {
    start_color := by rw [←hs]; exact r.start_color
    walk := r.walk.copy hs rfl
    shortest := by rw [SimpleGraph.Walk.length_copy,r.shortest,hs]
    critical := by simpa only [hs] using r.critical }
  have hr (i : ℕ) : r'.walk.getVert i = act d.radical g (q.walk.getVert i) := by
    change (r.walk.copy hs rfl).getVert i = _
    rw [SimpleGraph.Walk.getVert_copy]
    exact actWalk_getVert d.radical g q.walk i
  refine ⟨_,r',?_,?_⟩
  · rw [hr,hqm,hcancel]
  · rw [hr,hr,hr,Q_act,Q_act,stabilizer_act,←Subgroup.map_sup,hqgen]

private theorem strict_generated_forward_path_of_opposite_slice
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hopposite : 2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z)) :
    ∃ w, ∃ q : CriticalPath d.radical (replacementGeometry h d) a w,
      q.walk.getVert 2 = p.walk.getVert 2 ∧
      Q d.radical (q.walk.getVert 1) ⊔ Q d.radical (q.walk.getVert 3) =
        stabilizer d.radical (q.walk.getVert 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨b⟩ := mixed_strict_backward_shift_at_knownSimple hb u him p hstrict
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  let b' : CriticalPath d.radical (replacementGeometry h d) b.start (p.walk.getVert 2) := {
    start_color := b.path.start_color
    walk := b.path.walk.copy rfl he
    shortest := by rw [SimpleGraph.Walk.length_copy,b.path.shortest,he]
    critical := by simpa only [he] using b.path.critical }
  have hbl : b'.walk.length = 4 := b'.length_eq_b.trans hb
  have hbm : b'.walk.getVert 2 = a := by
    simpa only [b',SimpleGraph.Walk.getVert_copy,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
      using b.overlap 0 (Nat.zero_le _)
  let r : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) b.start :=
    ⟨b'.end_color,b'.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,b'.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc b'⟩
  have hrm : r.walk.getVert 2 = a := by
    change b'.walk.reverse.getVert 2 = a
    rw [SimpleGraph.Walk.getVert_reverse,hbl]
    exact hbm
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent d.radical z (p.walk.getVert 3) := by
    have hh := (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 3) (by omega))
    have hend : p.walk.getVert 4 = z := by simpa only [hl] using p.walk.getVert_length
    rw [show 3+1=4 from rfl,hend] at hh
    exact adjacent_symm d.radical hh
  obtain ⟨w,q,hqm,hqgen⟩ := generated_reciprocal_path_of_strict_neighbor_at
    hb u him r hct hzt hopposite
  let q' : CriticalPath d.radical (replacementGeometry h d) a w := {
    start_color := p.start_color
    walk := q.walk.copy hrm rfl
    shortest := by rw [SimpleGraph.Walk.length_copy,q.shortest,hrm]
    critical := by simpa only [hrm] using q.critical }
  refine ⟨w,q',?_,?_⟩
  · simpa only [q',SimpleGraph.Walk.getVert_copy] using hqm
  · simpa only [q',SimpleGraph.Walk.getVert_copy] using hqgen

/-- Every strict mixed critical slice has a critical path with the same
starting vertex and midpoint, whose interior edge kernels generate the full
midpoint stabilizer. The original strict slice is therefore retained. -/
theorem strict_generated_forward_path_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ w, ∃ q : CriticalPath d.radical (replacementGeometry h d) a w,
      q.walk.getVert 2 = p.walk.getVert 2 ∧
      Q d.radical (q.walk.getVert 1) ⊔ Q d.radical (q.walk.getVert 3) =
        stabilizer d.radical (q.walk.getVert 2) := by
  exact strict_generated_forward_path_of_opposite_slice hb u him p hstrict
    (strict_opposite_slice_at_knownSimple hb u him p hstrict)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
