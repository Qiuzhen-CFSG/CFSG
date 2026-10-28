module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# Equal-mover shifts on the original critical walk

The paired trapped exclusion supplies a backward path in one of two
orientations. Pull the second orientation back by the same residual
conjugator, retaining the selected generating edge and every overlapping
vertex. Transport this single-walk result to every component vertex.

If a radius is trapped in its predecessor core, the large-critical-image
escape first makes the critical index small. The new shift then bounds
every equal-mover neighbor slice by two, at every component vertex.
Consequently a strict trapped slice has unequal movers, so their established
nonquadratic comparison and exact fixed index eight apply. At an equal-mover
last edge, the slice bound identifies the full reverse critical kernel and
both critical indices; its central attachment is retained.

The final application uses the original radical's literal restriction and
embedding. Its source small mover is carried by the same graph transporter,
and the slice index is preserved exactly. Both moving covers of orders
sixteen and thirty-two remain allowed. Unequal-mover selection, residual
commutator alignment, and the final distance exclusions remain separate
obligations in this owner.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7)--(5.8), printed pp.919--920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Resolve both paired orientations into one backward shift of the original
critical walk, preserving its generating edge. -/
theorem sixteen_equal_mover_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hequal : SmallMover.join (U d.radical delta) (Q d.radical delta)
        (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨t,hat,g,hg,hgt,hct,hi,x,hx,_,q,hq,_,_,hgen,_,_,_,_,_,_,hat₂,hct₂,hi₂,_,hgen₂,_,_,halt⟩ :=
    sixteen_equal_mover_strict_backward_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hdelta hequal hstrict
  rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
  · exact ⟨t,hat,g,hg,hgt,hct,hgen,hi,v,hvt,hover⟩
  · let y := g*x⁻¹
    have hy : y ∈ stabilizer d.radical (alpha d.radical) :=
      mul_mem hg (inv_mem (Ltilde_le_stabilizer _ hx))
    have hyt : act d.radical y (p.walk.getVert 1) = act d.radical x⁻¹ t := by
      rw [show y=g*x⁻¹ from rfl,act_mul,hgt]
    have hstart : act d.radical x⁻¹ (act d.radical g delta) = act d.radical y delta :=
      (act_mul d.radical g x⁻¹ delta).symm
    rw [hstart] at hct₂ hi₂
    refine ⟨act d.radical x⁻¹ t,hat₂,y,hy,hyt,hct₂,hgen₂,hi₂,?_⟩
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
    have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x⁻¹ (act d.radical g delta))
        (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
        w.walk.getVert 1 = act d.radical x⁻¹ t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2) = p.walk.getVert i := by
      refine ⟨v.act x⁻¹,?_,?_⟩
      · simp only [CriticalPath.act,actWalk_getVert,hvt]
      · intro i hi
        have hiq : i ≤ q.walk.length-2 := hlen.symm ▸ hi
        simp only [CriticalPath.act,actWalk_getVert,hover i hiq,hq,
          ←act_mul,mul_inv_cancel,act_one]
    rwa [hstart,hend] at hex

include e hz hn in
/-- The same generating backward shift at every original component vertex. -/
theorem sixteen_equal_mover_backward_shift_at_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hequal : SmallMover.join (U d.radical delta) (Q d.radical delta)
        (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ g ∈ stabilizer d.radical a,
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := sixteen_equal_mover_backward_shift_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard
    (z := act d.radical j⁻¹ z) (delta := act d.radical j⁻¹ delta)
  rw [←hbase] at base
  have hdelta0 : Adjacent d.radical (act d.radical j⁻¹ delta)
      ((p.act j⁻¹).walk.getVert 1) := by
    simpa only [CriticalPath.act,actWalk_getVert] using
      (adjacent_act_iff d.radical j⁻¹ _ _).mpr hdelta
  have hindex0 : 2 < (B d.radical (act d.radical j⁻¹ a)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical j⁻¹ delta)) := by
    rw [Escape.PairingControl.FirstPairing.B_act hb2 j⁻¹ a p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  have hsmall0 : (Q d.radical (act d.radical j⁻¹ z)).relIndex
      (Z d.radical (act d.radical j⁻¹ a)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hsmall
  have hequal0 : SmallMover.join (U d.radical (act d.radical j⁻¹ delta))
      (Q d.radical (act d.radical j⁻¹ delta)) (Q d.radical ((p.act j⁻¹).walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (act d.radical j⁻¹ a)) (Q d.radical (act d.radical j⁻¹ a))
        (Q d.radical ((p.act j⁻¹).walk.getVert 1)) 4 := by
    have hh := congrArg (Subgroup.map (MulAut.conj (j⁻¹)⁻¹).toMonoidHom) hequal
    rw [SmallMover.join_map _ (MulAut.conj (j⁻¹)⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj (j⁻¹)⁻¹).injective,←U_act,←Q_act,←Q_act,←U_act,←Q_act] at hh
    simpa only [CriticalPath.act,actWalk_getVert] using hh
  obtain ⟨t,hat,k,hk,hkt,hct,hgen,_,v,hvt,hover⟩ :=
    base (p.act j⁻¹) hsmall0 hdelta0 hequal0 hindex0
  have hcancel (v : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  let y := j⁻¹*k*j
  have hact (v : Vertex d.radical) : act d.radical j (act d.radical k (act d.radical j⁻¹ v)) =
      act d.radical y v := by simp only [←act_mul,y,mul_assoc]
  have hy : y ∈ stabilizer d.radical a := by
    change act d.radical y a = a
    rw [←hact]
    rw [show act d.radical k (act d.radical j⁻¹ a)=act d.radical j⁻¹ a from hk,hcancel]
  have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj y⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 a p.start_color ((stabilizer d.radical a).inv_mem hy))
  have hstrict' : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical y delta)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hstrict
  refine ⟨act d.radical j t,?_,y,hy,?_,?_,?_,hstrict',?_⟩
  · simpa only [hcancel] using (adjacent_act_iff d.radical j _ _).mpr hat
  · have he := congrArg (act d.radical j) hkt
    simpa only [CriticalPath.act,actWalk_getVert,hact] using he
  · simpa only [hact] using (adjacent_act_iff d.radical j _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj j⁻¹).toMonoidHom) hgen
    rwa [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
  · have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical j (act d.radical k (act d.radical j⁻¹ delta)))
        (act d.radical j ((p.act j⁻¹).walk.getVert ((p.act j⁻¹).walk.length-2))),
        w.walk.getVert 1=act d.radical j t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
      refine ⟨v.act j,?_,?_⟩
      · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical j) hvt
      · intro i hi
        have he := congrArg (act d.radical j) (hover i (by
          simpa only [CriticalPath.act,actWalk_length] using hi))
        simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
    have hend : act d.radical j ((p.act j⁻¹).walk.getVert ((p.act j⁻¹).walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      simp only [CriticalPath.act,actWalk_length,actWalk_getVert,hcancel]
    rwa [hact,hend] at hex

include e hz hn in
/-- Trapping bounds every equal-mover neighbor slice at the starting vertex.
The critical-index premise is discharged by the large-image escape. -/
theorem sixteen_trapped_equal_mover_slice_le_two_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  by_contra! hstrict
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4 := by
    by_contra! hlarge
    exact SylowLarge.sixteen_large_image_radius_escape_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard p hlarge htrap
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hfirst : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨j,hj,hjt⟩ := stabilizer_transitive_neighbors d.radical a hat hfirst
  have hdelta : Adjacent d.radical (act d.radical j c) (p.walk.getVert 1) := by
    rw [←hjt]
    exact (adjacent_act_iff d.radical j _ _).mpr hct
  have hja : act d.radical j a = a := hj
  have hequal' : SmallMover.join (U d.radical (act d.radical j c))
      (Q d.radical (act d.radical j c)) (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4 := by
    have hh := congrArg (Subgroup.map (MulAut.conj j⁻¹).toMonoidHom) hequal
    rwa [SmallMover.join_map _ (MulAut.conj j⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj j⁻¹).injective,←U_act,←Q_act,←Q_act,←U_act,←Q_act,hja,hjt] at hh
  have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj j⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 a p.start_color ((stabilizer d.radical a).inv_mem hj))
  have hi : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical j c)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj j⁻¹).injective]
    exact hstrict
  obtain ⟨v,hav,g,hg,hgt,hcv,_,_,q,_⟩ :=
    sixteen_equal_mover_backward_shift_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hdelta hequal' hi
  have hdist : (cosetGraph d.radical).dist (act d.radical g (act d.radical j c)) a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist (act d.radical g (act d.radical j c)) v = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hcv)
    have h2 : (cosetGraph d.radical).dist v a = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hav))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := act d.radical g (act d.radical j c)) (v := v) (w := a)
  exact q.critical.2 (((Z_le_localZSpan d.radical _ _).trans
    (localZSpan_le_V d.radical hdist)).trans htrap)

include e hz hn in
/-- One trapped radius bounds equal-mover slices at every original component
vertex, with no restriction to the trapped path's first edge. -/
theorem sixteen_trapped_all_equal_slices_le_two_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical ha
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  let y := g⁻¹*j
  have hya : act d.radical y a = a₀ := by
    rw [hg,hj,act_mVertex]
    simp only [y,mul_inv_cancel_left]
  have hyt : Adjacent d.radical a₀ (act d.radical y t) := by
    rw [←hya]
    exact (adjacent_act_iff d.radical y _ _).mpr hat
  have hequal' : SmallMover.join (U d.radical (act d.radical y c))
      (Q d.radical (act d.radical y c)) (Q d.radical (act d.radical y t)) 4 =
      SmallMover.join (U d.radical a₀) (Q d.radical a₀) (Q d.radical (act d.radical y t)) 4 := by
    have hh := congrArg (Subgroup.map (MulAut.conj y⁻¹).toMonoidHom) hequal
    rwa [SmallMover.join_map _ (MulAut.conj y⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj y⁻¹).injective,←U_act,←Q_act,←Q_act,←U_act,←Q_act,hya] at hh
  have hh := sixteen_trapped_equal_mover_slice_le_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p htrap hyt
      ((adjacent_act_iff d.radical y _ _).mpr hct) hequal'
  rw [←hya,Escape.PairingControl.FirstPairing.B_act (by omega : 2 < replacementDistance h d)
    y a ha,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective] at hh
  exact hh

include e hz hn in
/-- On an equal-mover last edge, trapping identifies the actual full reverse
kernel with the predecessor slice and forces both critical indices to two. -/
theorem sixteen_trapped_equal_predecessor_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a')
    (hequal : SmallMover.join (U d.radical a') (Q d.radical a')
        (Q d.radical (q.walk.getVert (q.walk.length-1))) 4 =
      SmallMover.join (U d.radical (q.walk.getVert (q.walk.length-2)))
        (Q d.radical (q.walk.getVert (q.walk.length-2)))
        (Q d.radical (q.walk.getVert (q.walk.length-1))) 4) :
    Z d.radical a' ⊓ B d.radical (q.walk.getVert (q.walk.length-2))
        ((replacementGeometry h d).Z_normal _) = Z d.radical a' ⊓ Q d.radical a ∧
      (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < q.walk.length := q.length_eq_b ▸ hb2
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hct : Adjacent d.radical (q.walk.getVert (q.walk.length-2))
      (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  exact critical_predecessor_slice_eq_kernel s hc hb2 q
    (sixteen_trapped_all_equal_slices_le_two_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hcard p htrap hcol hct het hequal)

include e hz hn in
/-- A strict trapped slice must use unequal movers. Apply their actual
nonquadratic comparison and exact index-eight fixed-subgroup bound. -/
theorem sixteen_trapped_strict_neighbor_control_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    E ≠ J ∧ J ⊔ E = Q d.radical t ∧ (J ⊓ E).relIndex (Q d.radical t) = 4 ∧
      ⁅⁅U d.radical a,E⁆,E⁆ ≠ ⊥ ∧ ⁅⁅U d.radical c,J⁆,J⁆ ≠ ⊥ ∧
      (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 8 := by
  have hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 := by
    intro heq
    exact (Nat.not_le_of_gt hstrict) (sixteen_trapped_equal_mover_slice_le_two_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p htrap hat hct heq)
  obtain ⟨hjoin,hidx,hquad,hquad'⟩ := SylowAdjacent.sixteen_unequal_neighbor_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hne
  exact ⟨hne,hjoin,hidx,hquad,hquad',
    SylowKernelMovement.sixteen_unequal_neighbor_fixed_index_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hne⟩

include e hz hn in
/-- The original restricted radical and its small mover use the same
transporter as the backward path; the exact slice index is preserved. -/
theorem original_radical_equal_mover_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hequal : SmallMover.join (U d.radical delta) (Q d.radical delta) (Q d.radical (beta d.radical)) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (beta d.radical)) 4)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let J := SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical)) T 4
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (beta d.radical) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        T.map (MulAut.conj g⁻¹).toMonoidHom = Q d.radical t ∧
        J.map (MulAut.conj g⁻¹).toMonoidHom =
          SmallMover.join (U d.radical (act d.radical g delta))
            (Q d.radical (act d.radical g delta)) (Q d.radical t) 4 ∧
        T.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (act d.radical g delta)) =
          (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical delta) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,_,q,hqt,hover⟩ :=
    sixteen_equal_mover_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
      (by rwa [hfirst]) (by rwa [hfirst]) hstrict
  rw [hfirst] at hgt
  have hrestriction := (SylowLarge.sixteen_original_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 hcard).2.1
  have hT : ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) =
      Q d.radical (beta d.radical) := by
    rw [Q_beta]
    exact congrArg (Subgroup.map (embedM d.radical)) hrestriction.symm
  have hTg : (((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map
      (embedM d.radical)).map (MulAut.conj g⁻¹).toMonoidHom = Q d.radical t := by
    rw [hT,←Q_act,hgt]
  refine ⟨t,hat,g,hg,hgt,hct,hTg,?_,?_,?_,q,hqt,hover⟩
  · rw [hT,←hequal,SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      ←U_act,←Q_act,←Q_act,hgt]
  · rwa [hTg]
  · have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective,hB]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
