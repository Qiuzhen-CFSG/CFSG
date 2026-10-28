module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowUnequalResidual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowEqualShift

/-!
# Complete strict backward shifts in the order-sixteen radical image

For unequal neighboring movers, transport the candidate to the existing
selected generating edge. The mover inequality is transported by the same
conjugator. SylowUnequalResidual excludes its trapped alternative, so the
candidate starts a backward critical walk with every original overlap.
Combining with the checked equal-mover branch removes the mover comparison
from the strict-slice backward theorem.

If a whole radius were trapped, every neighboring slice would consequently
have index at most two: a strict slice would supply a critical seed inside
that same trapped radius. The large-critical-image escape discharges the
small-index premise. Conjugation transports this bound to every component
vertex. The existing predecessor-slice theorem then identifies each full
reverse kernel, retaining the two critical indices.

The original-radical application keeps the literal restricted radical, the
candidate's own small mover, the exact slice index, the same transporter,
and all vertices of the backward walk. Both moving-cover orders and full
central attachments remain. This completes the image-sixteen strict shift;
residual rotation and radius escape, the subsequent strict forward bounds,
image-eight and distance-four exclusions, and unconditional distance two
remain with the large-distance assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.8), printed pp.915--920.
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
/-- An unequal mover supplies a backward critical path on the selected generating edge. -/
theorem sixteen_unequal_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hne : SmallMover.join (U d.radical delta) (Q d.radical delta)
        (Q d.radical (p.walk.getVert 1)) 4 ≠
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
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,hnorm,halt⟩ :=
    SylowSpanSelection.sixteen_strict_backward_alternative_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hdelta hstrict
  have hga : act d.radical g a = a := hg
  have hne' : SmallMover.join (U d.radical (act d.radical g delta))
      (Q d.radical (act d.radical g delta)) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 := by
    intro he
    apply hne
    apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    rwa [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,←U_act,←Q_act,hga,hgt]
  refine ⟨t,hat,g,hg,hgt,hct,hgen,hi,?_⟩
  rcases halt with hpath | htrap
  · exact hpath
  · exact (sixteen_unequal_trapped_strict_impossible_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hat hct hne' hgen htrap.1 hnorm hi).elim

include e hz hn in
/-- Every strict small-critical slice has a backward shift, with no mover-equality premise. -/
theorem sixteen_strict_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
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
  by_cases heq : SmallMover.join (U d.radical delta) (Q d.radical delta)
      (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4
  · exact sixteen_equal_mover_backward_shift_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hdelta heq hstrict
  · exact sixteen_unequal_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hdelta heq hstrict

include e hz hn in
/-- A trapped radius bounds every neighboring slice by two. -/
theorem sixteen_trapped_slice_le_two_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
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
  have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj j⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 a p.start_color ((stabilizer d.radical a).inv_mem hj))
  have hi : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical j c)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj j⁻¹).injective]
    exact hstrict
  obtain ⟨v,hav,g,hg,hgt,hcv,_,_,q,_⟩ :=
    sixteen_strict_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hdelta hi
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
/-- One trapped radius bounds all slices at every component vertex. -/
theorem sixteen_trapped_all_slices_le_two_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
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
  have hh := sixteen_trapped_slice_le_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p htrap hyt
      ((adjacent_act_iff d.radical y _ _).mpr hct)
  rw [←hya,Escape.PairingControl.FirstPairing.B_act (by omega : 2 < replacementDistance h d)
    y a ha,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective] at hh
  exact hh

include e hz hn in
/-- Trapping identifies every full predecessor slice with its literal reverse kernel. -/
theorem sixteen_trapped_predecessor_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a') :
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
    (sixteen_trapped_all_slices_le_two_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hcard p htrap hcol hct het)

include e hz hn in
/-- The original radical and candidate mover use the same backward transporter. -/
theorem original_radical_strict_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let J := SmallMover.join (U d.radical delta) (Q d.radical delta) T 4
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
    sixteen_strict_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
      (by rwa [hfirst]) hstrict
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
  · rw [hT,SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      ←U_act,←Q_act,←Q_act,hgt]
  · rwa [hTg]
  · have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective,hB]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
